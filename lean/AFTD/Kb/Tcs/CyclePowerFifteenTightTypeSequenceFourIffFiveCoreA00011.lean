import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a00011

Topic: combinatorics   Node: 1e027a2ea3c3

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_four_iff_five_core: under the layer-free tight-cover constraints for k = 15 and 37 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a00010.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a00010 (x : ℤ → Fin 16 → Bool)
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
    (g2 : (x (-2) 2).toNat = 0)
    (g3 : (x (-2) 6).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-1) 5).toNat = 0)
    (g6 : (x (-1) 13).toNat = 0)
    (g7 : (x 0 2).toNat = 0)
    (g8 : (x 0 3).toNat = 0)
    (g9 : (x 0 4).toNat = 1)
    (g10 : (x 0 5).toNat = 0)
    (g11 : (x 0 10).toNat = 0)
    (g12 : (x 0 11).toNat = 0)
    (g13 : (x 1 2).toNat = 0)
    (g14 : (x 1 6).toNat = 0)
    (g15 : (x 1 10).toNat = 0)
    (g16 : (x 2 10).toNat = 0)
    (g17 : (x 3 9).toNat = 0)
    (g18 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g19 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g20 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g21 : (x 4 4 && x 4 8).toNat = 0)
    (g22 : (x 3 5 && x 3 9).toNat = 0)
    (g23 : (x 2 6 && x 2 10).toNat = 0)
    (g24 : (x 1 7 && x 1 11).toNat = 0)
    (g25 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g26 : (x 0 4 && x 0 10).toNat = 0)
    (g27 : (x (-1) 5 && x (-1) 11).toNat = 0)
    (g28 : (x (-2) 6 && x (-2) 12).toNat = 0)
    (g29 : (x (-3) 7 && x (-3) 13).toNat = 0)
    (g30 : (x 4 2 && x 4 8).toNat = 0)
    (g31 : (x 3 3 && x 3 9).toNat = 0)
    (g32 : (x 2 4 && x 2 10).toNat = 0)
    (g33 : (x 1 5 && x 1 11).toNat = 0)
    (g34 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g35 : (x 2 1 && x 2 10).toNat = 0)
    (g36 : (x 1 2 && x 1 11).toNat = 0)
    (g37 : (x 0 3 && x 0 12).toNat = 0)
    (g38 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g39 : (x 0 5 && x 0 14).toNat = 0)
    (g40 : (x 1 5 && x 1 14).toNat = 0)
    (g41 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g42 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g43 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g44 : (x 1 1 && x 1 11).toNat = 0)
    (g45 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g46 : (x 1 2 && x 1 12).toNat = 0)
    (g47 : (x 0 3 && x 0 13).toNat = 0)
    (g48 : (x 1 4 && x 1 14).toNat = 0)
    (g49 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g50 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g51 : (x 1 2 && x 1 13).toNat = 0)
    (g52 : (x 0 3 && x 0 14).toNat = 0)
    (g53 : (x 1 1 && x 1 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d12210 : (x 0 2 && x 0 12).toNat = 0 := by
    have r12211 := hand1 (x 0 2) (x 0 12)
    have b12212 := hb (x 0 2)
    have b12213 := hb (x 0 2 && x 0 12)
    clear * - r12211 b12212 b12213 g7
    omega
  have d12214 : (x 0 2 && x 0 9).toNat = 0 := by
    have r12215 := hand1 (x 0 2) (x 0 9)
    have b12216 := hb (x 0 2)
    have b12217 := hb (x 0 2 && x 0 9)
    clear * - r12215 b12216 b12217 g7
    omega
  have d12218 : (x 2 13).toNat = 1 := by
    have r12219 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12220 := hb (x 0 2)
    have b12221 := hb (x 2 13)
    have b12222 := hb (x 1 1 && x 1 14)
    clear * - r12219 b12220 b12221 b12222 g53 g7
    omega
  have d12223 : (x 2 1).toNat = 1 := by
    have r12224 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
    have b12225 := hb (x 2 1)
    have b12226 := hb (x 2 13)
    clear * - r12224 b12225 b12226 d12218
    omega
  have d12227 : (x 3 14).toNat = 0 := by
    have r12228 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12229 := hb (x 2 1)
    have b12230 := hb (x 3 14)
    clear * - r12228 b12229 b12230 d12223
    omega
  have d12231 : (x 3 1 && x 3 14).toNat = 0 := by
    have r12232 := hand2 (x 3 1) (x 3 14)
    have b12233 := hb (x 3 14)
    have b12234 := hb (x 3 1 && x 3 14)
    clear * - r12232 b12233 b12234 d12227
    omega
  have d12235 : (x 3 3 && x 3 14).toNat = 0 := by
    have r12236 := hand2 (x 3 3) (x 3 14)
    have b12237 := hb (x 3 14)
    have b12238 := hb (x 3 3 && x 3 14)
    clear * - r12236 b12237 b12238 d12227
    omega
  have d12239 : (x 3 6).toNat = 0 := by
    have r12240 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
    have b12241 := hb (x 3 6)
    have b12242 := hb (x 3 14)
    clear * - r12240 b12241 b12242 d12227
    omega
  have d12243 : (x 3 2).toNat = 0 := by
    have r12244 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b12245 := hb (x 3 2)
    have b12246 := hb (x 3 14)
    clear * - r12244 b12245 b12246 d12227
    omega
  have d12247 : (x 3 2 && x 3 12).toNat = 0 := by
    have r12248 := hand1 (x 3 2) (x 3 12)
    have b12249 := hb (x 3 2)
    have b12250 := hb (x 3 2 && x 3 12)
    clear * - r12248 b12249 b12250 d12243
    omega
  have d12251 : (x 3 2 && x 3 11).toNat = 0 := by
    have r12252 := hand1 (x 3 2) (x 3 11)
    have b12253 := hb (x 3 2)
    have b12254 := hb (x 3 2 && x 3 11)
    clear * - r12252 b12253 b12254 d12243
    omega
  have d12255 : (x 3 10).toNat = 0 := by
    have r12256 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
    have b12257 := hb (x 3 2)
    have b12258 := hb (x 3 10)
    clear * - r12256 b12257 b12258 d12243
    omega
  have d12259 : (x 3 12).toNat = 0 := by
    have r12260 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12261 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e12262 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b12263 := hb (x 0 3)
    have b12264 := hb (x 1 2)
    have b12265 := hb (x 2 13)
    have b12266 := hb (x 3 12)
    clear * - r12260 e12261 e12262 b12263 b12264 b12265 b12266 d12218 g13 g8
    omega
  have d12267 : (x 3 3 && x 3 12).toNat = 0 := by
    have r12268 := hand2 (x 3 3) (x 3 12)
    have b12269 := hb (x 3 12)
    have b12270 := hb (x 3 3 && x 3 12)
    clear * - r12268 b12269 b12270 d12259
    omega
  have d12271 : (x 3 4).toNat = 0 := by
    have r12272 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
    have b12273 := hb (x 3 4)
    have b12274 := hb (x 3 12)
    clear * - r12272 b12273 b12274 d12259
    omega
  have d12275 : (x 3 4 && x 3 13).toNat = 0 := by
    have r12276 := hand1 (x 3 4) (x 3 13)
    have b12277 := hb (x 3 4)
    have b12278 := hb (x 3 4 && x 3 13)
    clear * - r12276 b12277 b12278 d12271
    omega
  cases h12279 : x 0 6
  · have f12280 : (x 0 6).toNat = 0 := by rw [h12279]; rfl
    have d12281 : (x 0 6 && x 0 12).toNat = 0 := by
      have r12282 := hand1 (x 0 6) (x 0 12)
      have b12283 := hb (x 0 6)
      have b12284 := hb (x 0 6 && x 0 12)
      clear * - r12282 b12283 b12284 f12280
      omega
    cases h12285 : x 0 7
    · have f12286 : (x 0 7).toNat = 0 := by rw [h12285]; rfl
      cases h12287 : x 0 8
      · have f12288 : (x 0 8).toNat = 0 := by rw [h12287]; rfl
        have d12289 : (x 0 8 && x 0 12).toNat = 0 := by
          have r12290 := hand1 (x 0 8) (x 0 12)
          have b12291 := hb (x 0 8)
          have b12292 := hb (x 0 8 && x 0 12)
          clear * - r12290 b12291 b12292 f12288
          omega
        have r12293 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12294 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
        have e12295 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
        have e12296 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
        have e12297 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
        have e12298 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
        have e12299 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
        have r12300 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12301 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
        have e12302 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
        have e12303 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
        have e12304 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
        have e12305 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
        have e12306 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
        have r12307 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12308 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
        have e12309 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
        have e12310 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
        have e12311 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
        have e12312 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
        have e12313 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
        have r12314 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12315 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
        have e12316 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
        have e12317 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
        have e12318 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
        have e12319 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
        have e12320 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
        have r12321 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12322 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
        have e12323 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
        have e12324 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
        have e12325 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
        have e12326 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
        have e12327 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
        have r12328 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12329 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e12330 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have r12331 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12332 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
        have e12333 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
        have r12334 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12335 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e12336 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have r12337 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12338 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
        have e12339 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
        have r12340 : 1 ≤ (x 4 6).toNat + (x 3 1 && x 3 7).toNat + (x 2 2 && x 2 8).toNat + (x 1 3 && x 1 9).toNat + (x 0 4 && x 0 10).toNat + (x (-1) 5 && x (-1) 11).toNat + (x (-2) 6 && x (-2) 12).toNat + (x (-3) 7 && x (-3) 13).toNat + (x (-4) 8 && x (-4) 14).toNat + (x (-5) 9).toNat := by have q := hcov6 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r12341 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r12342 : 1 ≤ (x (-4) 10).toNat + (x (-5) 1 && x (-5) 11).toNat + (x (-6) 2 && x (-6) 12).toNat + (x (-7) 3 && x (-7) 13).toNat + (x (-8) 4 && x (-8) 14).toNat + (x (-9) 5).toNat := by have q := hcov10 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r12343 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r12344 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r12345 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r12346 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have r12347 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
        have r12348 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
        have r12349 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
        have r12350 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
        have r12351 := hand1 (x 6 2) (x 6 6)
        have r12352 := hand1 (x 5 3) (x 5 7)
        have r12353 := hand2 (x 3 1) (x 3 7)
        have r12354 := hand2 (x 2 2) (x 2 8)
        have r12355 := hand2 (x 1 3) (x 1 9)
        have r12356 := hand1 (x (-4) 8) (x (-4) 14)
        have r12357 := hand2 (x 5 1) (x 5 7)
        have r12358 := hand1 (x (-2) 8) (x (-2) 14)
        have r12359 := hand2 (x (-5) 1) (x (-5) 11)
        have r12360 := hand1 (x (-6) 2) (x (-6) 12)
        have r12361 := hand1 (x (-7) 3) (x (-7) 13)
        have r12362 := hand1 (x (-8) 4) (x (-8) 14)
        have r12363 := hand1 (x (-4) 2) (x (-4) 12)
        have r12364 := hand1 (x (-5) 3) (x (-5) 13)
        have r12365 := hand1 (x (-6) 4) (x (-6) 14)
        have r12366 := hand2 (x (-1) 1) (x (-1) 11)
        have r12367 := hand1 (x (-4) 4) (x (-4) 14)
        have r12368 := hand1 (x (-2) 4) (x (-2) 14)
        have r12369 := hand2 (x 9 1) (x 9 11)
        have r12370 := hand2 (x 8 2) (x 8 12)
        have r12371 := hand2 (x 7 3) (x 7 13)
        have r12372 := hand1 (x 6 4) (x 6 14)
        linarith only [r12293, e12294, e12295, e12296, e12297, e12298, e12299, r12300, e12301, e12302, e12303, e12304, e12305, e12306, r12307, e12308, e12309, e12310, e12311, e12312, e12313, r12314, e12315, e12316, e12317, e12318, e12319, e12320, r12321, e12322, e12323, e12324, e12325, e12326, e12327, r12328, e12329, e12330, r12331, e12332, e12333, r12334, e12335, e12336, r12337, e12338, e12339, r12340, r12341, r12342, r12343, r12344, r12345, r12346, r12347, r12348, r12349, r12350, r12351, r12352, r12353, r12354, r12355, r12356, r12357, r12358, r12359, r12360, r12361, r12362, r12363, r12364, r12365, r12366, r12367, r12368, r12369, r12370, r12371, r12372, g1, g4, g11, g16, g21, g22, g23, g24, d12289, g25, g26, g27, g28, g29, g30, g31, g32, g33, d12281, g34, g41, g42, g43, g44, d12210, g45]
      · have f12474 : (x 0 8).toNat = 1 := by rw [h12287]; rfl
        have d12475 : (x (-1) 9).toNat = 0 := by
          have r12476 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12477 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e12478 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e12479 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e12480 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e12481 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e12482 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b12483 := hb (x (-7) 7)
          have b12484 := hb (x (-6) 6)
          have b12485 := hb (x (-5) 5)
          have b12486 := hb (x (-4) 4)
          have b12487 := hb (x (-3) 11)
          have b12488 := hb (x (-2) 10)
          have b12489 := hb (x (-1) 9)
          have b12490 := hb (x 0 8)
          clear * - r12476 e12477 e12478 e12479 e12480 e12481 e12482 b12483 b12484 b12485 b12486 b12487 b12488 b12489 b12490 f12474 g4 g1
          omega
        have d12491 : (x (-4) 4).toNat = 0 := by
          have r12492 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12493 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e12494 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e12495 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e12496 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e12497 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e12498 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b12499 := hb (x (-7) 7)
          have b12500 := hb (x (-6) 6)
          have b12501 := hb (x (-5) 5)
          have b12502 := hb (x (-4) 4)
          have b12503 := hb (x (-3) 11)
          have b12504 := hb (x (-2) 10)
          have b12505 := hb (x (-1) 9)
          have b12506 := hb (x 0 8)
          clear * - r12492 e12493 e12494 e12495 e12496 e12497 e12498 b12499 b12500 b12501 b12502 b12503 b12504 b12505 b12506 f12474 d12475 g4 g1
          omega
        have d12507 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
          have r12508 := hand1 (x (-4) 4) (x (-4) 14)
          have b12509 := hb (x (-4) 4)
          have b12510 := hb (x (-4) 4 && x (-4) 14)
          clear * - r12508 b12509 b12510 d12491
          omega
        have d12511 : (x (-1) 1 && x (-1) 12).toNat = 1 := by
          have r12512 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12513 := hb (x (-4) 4)
          have b12514 := hb (x 0 11)
          have b12515 := hb (x (-1) 1 && x (-1) 12)
          have b12516 := hb (x (-2) 2 && x (-2) 13)
          have b12517 := hb (x (-3) 3 && x (-3) 14)
          clear * - r12512 b12513 b12514 b12515 b12516 b12517 g12 g49 g50 d12491
          omega
        have d12518 : (x (-1) 12).toNat = 1 := by
          have r12519 := hand2 (x (-1) 1) (x (-1) 12)
          have b12520 := hb (x (-1) 12)
          have b12521 := hb (x (-1) 1 && x (-1) 12)
          clear * - r12519 b12520 b12521 d12511
          omega
        have d12522 : (x (-2) 13).toNat = 0 := by
          have r12523 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12524 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e12525 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b12526 := hb (x (-4) 3)
          have b12527 := hb (x (-3) 2)
          have b12528 := hb (x (-2) 13)
          have b12529 := hb (x (-1) 12)
          clear * - r12523 e12524 e12525 b12526 b12527 b12528 b12529 d12518
          omega
        have d12530 : (x (-2) 5).toNat = 0 := by
          have r12531 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
          have b12532 := hb (x (-2) 5)
          have b12533 := hb (x (-2) 13)
          clear * - r12531 b12532 b12533 d12522
          omega
        have d12534 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
          have r12535 := hand1 (x (-2) 5) (x (-2) 14)
          have b12536 := hb (x (-2) 5)
          have b12537 := hb (x (-2) 5 && x (-2) 14)
          clear * - r12535 b12536 b12537 d12530
          omega
        have d12538 : (x (-3) 6).toNat = 1 := by
          have r12539 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12540 := hb (x (-3) 6)
          have b12541 := hb (x 3 9)
          have b12542 := hb (x 2 1 && x 2 10)
          have b12543 := hb (x 1 2 && x 1 11)
          have b12544 := hb (x 0 3 && x 0 12)
          have b12545 := hb (x (-1) 4 && x (-1) 13)
          have b12546 := hb (x (-2) 5 && x (-2) 14)
          clear * - r12539 b12540 b12541 b12542 b12543 b12544 b12545 b12546 g17 g35 g36 g37 g38 d12534
          omega
        have d12547 : (x (-3) 14).toNat = 1 := by
          have r12548 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
          have b12549 := hb (x (-3) 6)
          have b12550 := hb (x (-3) 14)
          clear * - r12548 b12549 b12550 d12538
          omega
        have d12551 : (x (-4) 1).toNat = 0 := by
          have r12552 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12553 := hb (x (-4) 1)
          have b12554 := hb (x (-3) 14)
          clear * - r12552 b12553 b12554 d12547
          omega
        have d12555 : (x (-4) 13).toNat = 0 := by
          have r12556 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
          have b12557 := hb (x (-4) 1)
          have b12558 := hb (x (-4) 13)
          clear * - r12556 b12557 b12558 d12551
          omega
        have d12559 : (x 3 8).toNat = 0 := by
          have r12560 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12561 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e12562 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e12563 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e12564 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e12565 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e12566 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b12567 := hb (x (-4) 7)
          have b12568 := hb (x (-3) 6)
          have b12569 := hb (x (-2) 5)
          have b12570 := hb (x (-1) 4)
          have b12571 := hb (x 0 11)
          have b12572 := hb (x 1 10)
          have b12573 := hb (x 2 9)
          have b12574 := hb (x 3 8)
          clear * - r12560 e12561 e12562 e12563 e12564 e12565 e12566 b12567 b12568 b12569 b12570 b12571 b12572 b12573 b12574 g15 g12 d12530 d12538
          omega
        have d12575 : (x 2 9).toNat = 0 := by
          have r12576 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12577 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e12578 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e12579 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e12580 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e12581 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e12582 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b12583 := hb (x (-4) 7)
          have b12584 := hb (x (-3) 6)
          have b12585 := hb (x (-2) 5)
          have b12586 := hb (x (-1) 4)
          have b12587 := hb (x 0 11)
          have b12588 := hb (x 1 10)
          have b12589 := hb (x 2 9)
          have b12590 := hb (x 3 8)
          clear * - r12576 e12577 e12578 e12579 e12580 e12581 e12582 b12583 b12584 b12585 b12586 b12587 b12588 b12589 b12590 d12559 g15 g12 d12530 d12538
          omega
        have d12591 : (x (-1) 4).toNat = 0 := by
          have r12592 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12593 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e12594 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e12595 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e12596 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e12597 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e12598 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b12599 := hb (x (-4) 7)
          have b12600 := hb (x (-3) 6)
          have b12601 := hb (x (-2) 5)
          have b12602 := hb (x (-1) 4)
          have b12603 := hb (x 0 11)
          have b12604 := hb (x 1 10)
          have b12605 := hb (x 2 9)
          have b12606 := hb (x 3 8)
          clear * - r12592 e12593 e12594 e12595 e12596 e12597 e12598 b12599 b12600 b12601 b12602 b12603 b12604 b12605 b12606 d12559 d12575 g15 g12 d12530 d12538
          omega
        have d12607 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
          have r12608 := hand1 (x (-1) 4) (x (-1) 14)
          have b12609 := hb (x (-1) 4)
          have b12610 := hb (x (-1) 4 && x (-1) 14)
          clear * - r12608 b12609 b12610 d12591
          omega
        have d12611 : (x 2 1 && x 2 11).toNat = 1 := by
          have r12612 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12613 := hb (x (-2) 5)
          have b12614 := hb (x 3 10)
          have b12615 := hb (x 2 1 && x 2 11)
          have b12616 := hb (x 1 2 && x 1 12)
          have b12617 := hb (x 0 3 && x 0 13)
          have b12618 := hb (x (-1) 4 && x (-1) 14)
          clear * - r12612 b12613 b12614 b12615 b12616 b12617 b12618 d12255 g46 g47 d12607 d12530
          omega
        have d12619 : (x 2 11).toNat = 1 := by
          have r12620 := hand2 (x 2 1) (x 2 11)
          have b12621 := hb (x 2 11)
          have b12622 := hb (x 2 1 && x 2 11)
          clear * - r12620 b12621 b12622 d12611
          omega
        have d12623 : (x 2 3).toNat = 1 := by
          have r12624 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
          have b12625 := hb (x 2 3)
          have b12626 := hb (x 2 11)
          clear * - r12624 b12625 b12626 d12619
          omega
        have d12627 : (x 5 12).toNat = 0 := by
          have r12628 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12629 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e12630 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b12631 := hb (x 2 3)
          have b12632 := hb (x 3 2)
          have b12633 := hb (x 4 13)
          have b12634 := hb (x 5 12)
          clear * - r12628 e12629 e12630 b12631 b12632 b12633 b12634 d12243 d12623
          omega
        have d12635 : (x 4 13).toNat = 0 := by
          have r12636 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12637 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e12638 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b12639 := hb (x 2 3)
          have b12640 := hb (x 3 2)
          have b12641 := hb (x 4 13)
          have b12642 := hb (x 5 12)
          clear * - r12636 e12637 e12638 b12639 b12640 b12641 b12642 d12627 d12243 d12623
          omega
        have d12643 : (x 2 2).toNat = 1 := by
          have r12644 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12645 := hb (x 2 2)
          have b12646 := hb (x 4 13)
          have b12647 := hb (x 3 1 && x 3 14)
          clear * - r12644 b12645 b12646 b12647 d12635 d12231
          omega
        have d12648 : (x 2 14).toNat = 1 := by
          have r12649 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
          have b12650 := hb (x 2 2)
          have b12651 := hb (x 2 14)
          clear * - r12649 b12650 b12651 d12643
          omega
        have d12652 : (x 1 1).toNat = 0 := by
          have r12653 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12654 := hb (x 1 1)
          have b12655 := hb (x 2 14)
          clear * - r12653 b12654 b12655 d12648
          omega
        have d12656 : (x 1 13).toNat = 0 := by
          have r12657 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
          have b12658 := hb (x 1 1)
          have b12659 := hb (x 1 13)
          clear * - r12657 b12658 b12659 d12652
          omega
        have d12660 : (x 4 12).toNat = 0 := by
          have r12661 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12662 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e12663 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b12664 := hb (x 1 3)
          have b12665 := hb (x 2 2)
          have b12666 := hb (x 3 13)
          have b12667 := hb (x 4 12)
          clear * - r12661 e12662 e12663 b12664 b12665 b12666 b12667 d12643
          omega
        have d12668 : (x 4 4).toNat = 0 := by
          have r12669 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b12670 := hb (x 4 4)
          have b12671 := hb (x 4 12)
          clear * - r12669 b12670 b12671 d12660
          omega
        have d12672 : (x 4 4 && x 4 14).toNat = 0 := by
          have r12673 := hand1 (x 4 4) (x 4 14)
          have b12674 := hb (x 4 4)
          have b12675 := hb (x 4 4 && x 4 14)
          clear * - r12673 b12674 b12675 d12668
          omega
        have d12676 : (x 3 13).toNat = 0 := by
          have r12677 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12678 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e12679 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b12680 := hb (x 1 3)
          have b12681 := hb (x 2 2)
          have b12682 := hb (x 3 13)
          have b12683 := hb (x 4 12)
          clear * - r12677 e12678 e12679 b12680 b12681 b12682 b12683 d12660 d12643
          omega
        have d12684 : (x 3 5).toNat = 0 := by
          have r12685 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
          have b12686 := hb (x 3 5)
          have b12687 := hb (x 3 13)
          clear * - r12685 b12686 b12687 d12676
          omega
        have d12688 : (x (-3) 2).toNat = 0 := by
          have r12689 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12690 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e12691 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b12692 := hb (x (-4) 3)
          have b12693 := hb (x (-3) 2)
          have b12694 := hb (x (-2) 13)
          have b12695 := hb (x (-1) 12)
          clear * - r12689 e12690 e12691 b12692 b12693 b12694 b12695 d12518 d12522
          omega
        have d12696 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
          have r12697 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12698 := hb (x (-3) 2)
          have b12699 := hb (x (-1) 13)
          have b12700 := hb (x (-2) 1 && x (-2) 14)
          clear * - r12697 b12698 b12699 b12700 g6 d12688
          omega
        have d12701 : (x (-2) 14).toNat = 1 := by
          have r12702 := hand2 (x (-2) 1) (x (-2) 14)
          have b12703 := hb (x (-2) 14)
          have b12704 := hb (x (-2) 1 && x (-2) 14)
          clear * - r12702 b12703 b12704 d12696
          omega
        have d12705 : (x (-3) 1).toNat = 0 := by
          have r12706 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12707 := hb (x (-3) 1)
          have b12708 := hb (x (-2) 14)
          clear * - r12706 b12707 b12708 d12701
          omega
        have d12709 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
          have r12710 := hand1 (x (-3) 1) (x (-3) 14)
          have b12711 := hb (x (-3) 1)
          have b12712 := hb (x (-3) 1 && x (-3) 14)
          clear * - r12710 b12711 b12712 d12705
          omega
        have d12713 : (x (-4) 2).toNat = 1 := by
          have r12714 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12715 := hb (x (-4) 2)
          have b12716 := hb (x (-2) 13)
          have b12717 := hb (x (-3) 1 && x (-3) 14)
          clear * - r12714 b12715 b12716 b12717 d12522 d12709
          omega
        have d12718 : (x (-4) 14).toNat = 1 := by
          have r12719 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
          have b12720 := hb (x (-4) 2)
          have b12721 := hb (x (-4) 14)
          clear * - r12719 b12720 b12721 d12713
          omega
        have d12722 : (x (-5) 1).toNat = 0 := by
          have r12723 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12724 := hb (x (-5) 1)
          have b12725 := hb (x (-4) 14)
          clear * - r12723 b12724 b12725 d12718
          omega
        have d12726 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
          have r12727 := hand1 (x (-5) 1) (x (-5) 14)
          have b12728 := hb (x (-5) 1)
          have b12729 := hb (x (-5) 1 && x (-5) 14)
          clear * - r12727 b12728 b12729 d12722
          omega
        have d12730 : (x (-6) 2).toNat = 1 := by
          have r12731 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12732 := hb (x (-6) 2)
          have b12733 := hb (x (-4) 13)
          have b12734 := hb (x (-5) 1 && x (-5) 14)
          clear * - r12731 b12732 b12733 b12734 d12555 d12726
          omega
        have d12735 : (x (-4) 12).toNat = 0 := by
          have r12736 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12737 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e12738 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b12739 := hb (x (-7) 3)
          have b12740 := hb (x (-6) 2)
          have b12741 := hb (x (-5) 13)
          have b12742 := hb (x (-4) 12)
          clear * - r12736 e12737 e12738 b12739 b12740 b12741 b12742 d12730
          omega
        have d12743 : (x (-5) 13).toNat = 0 := by
          have r12744 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12745 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e12746 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b12747 := hb (x (-7) 3)
          have b12748 := hb (x (-6) 2)
          have b12749 := hb (x (-5) 13)
          have b12750 := hb (x (-4) 12)
          clear * - r12744 e12745 e12746 b12747 b12748 b12749 b12750 d12735 d12730
          omega
        have d12751 : (x (-5) 5).toNat = 0 := by
          have r12752 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
          have b12753 := hb (x (-5) 5)
          have b12754 := hb (x (-5) 13)
          clear * - r12752 b12753 b12754 d12743
          omega
        have d12755 : (x (-1) 1 && x (-1) 11).toNat = 1 := by
          have r12756 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12757 := hb (x (-5) 5)
          have b12758 := hb (x 0 10)
          have b12759 := hb (x (-1) 1 && x (-1) 11)
          have b12760 := hb (x (-2) 2 && x (-2) 12)
          have b12761 := hb (x (-3) 3 && x (-3) 13)
          have b12762 := hb (x (-4) 4 && x (-4) 14)
          clear * - r12756 b12757 b12758 b12759 b12760 b12761 b12762 g11 g42 g43 d12507 d12751
          omega
        have d12763 : (x (-1) 11).toNat = 1 := by
          have r12764 := hand2 (x (-1) 1) (x (-1) 11)
          have b12765 := hb (x (-1) 11)
          have b12766 := hb (x (-1) 1 && x (-1) 11)
          clear * - r12764 b12765 b12766 d12755
          omega
        have d12767 : (x (-1) 3).toNat = 1 := by
          have r12768 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
          have b12769 := hb (x (-1) 3)
          have b12770 := hb (x (-1) 11)
          clear * - r12768 b12769 b12770 d12763
          omega
        have d12771 : (x 2 12).toNat = 0 := by
          have r12772 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12773 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e12774 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b12775 := hb (x (-1) 3)
          have b12776 := hb (x 0 2)
          have b12777 := hb (x 1 13)
          have b12778 := hb (x 2 12)
          clear * - r12772 e12773 e12774 b12775 b12776 b12777 b12778 d12656 g7 d12767
          omega
        have d12779 : (x 2 1 && x 2 12).toNat = 0 := by
          have r12780 := hand2 (x 2 1) (x 2 12)
          have b12781 := hb (x 2 12)
          have b12782 := hb (x 2 1 && x 2 12)
          clear * - r12780 b12781 b12782 d12771
          omega
        have d12783 : (x 3 11).toNat = 1 := by
          have r12784 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12785 := hb (x (-1) 4)
          have b12786 := hb (x 3 11)
          have b12787 := hb (x 2 1 && x 2 12)
          have b12788 := hb (x 1 2 && x 1 13)
          have b12789 := hb (x 0 3 && x 0 14)
          clear * - r12784 b12785 b12786 b12787 b12788 b12789 d12779 g51 g52 d12591
          omega
        have d12790 : (x 3 3).toNat = 1 := by
          have r12791 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
          have b12792 := hb (x 3 3)
          have b12793 := hb (x 3 11)
          clear * - r12791 b12792 b12793 d12783
          omega
        have d12794 : (x 6 12).toNat = 0 := by
          have r12795 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12796 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e12797 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b12798 := hb (x 3 3)
          have b12799 := hb (x 4 2)
          have b12800 := hb (x 5 13)
          have b12801 := hb (x 6 12)
          clear * - r12795 e12796 e12797 b12798 b12799 b12800 b12801 d12790
          omega
        have d12802 : (x 6 1 && x 6 12).toNat = 0 := by
          have r12803 := hand2 (x 6 1) (x 6 12)
          have b12804 := hb (x 6 12)
          have b12805 := hb (x 6 1 && x 6 12)
          clear * - r12803 b12804 b12805 d12794
          omega
        have d12806 : (x 6 2 && x 6 12).toNat = 0 := by
          have r12807 := hand2 (x 6 2) (x 6 12)
          have b12808 := hb (x 6 12)
          have b12809 := hb (x 6 2 && x 6 12)
          clear * - r12807 b12808 b12809 d12794
          omega
        have d12810 : (x 5 13).toNat = 0 := by
          have r12811 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12812 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e12813 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b12814 := hb (x 3 3)
          have b12815 := hb (x 4 2)
          have b12816 := hb (x 5 13)
          have b12817 := hb (x 6 12)
          clear * - r12811 e12812 e12813 b12814 b12815 b12816 b12817 d12794 d12790
          omega
        have d12818 : (x 5 2 && x 5 13).toNat = 0 := by
          have r12819 := hand2 (x 5 2) (x 5 13)
          have b12820 := hb (x 5 13)
          have b12821 := hb (x 5 2 && x 5 13)
          clear * - r12819 b12820 b12821 d12810
          omega
        have d12822 : (x 5 3 && x 5 13).toNat = 0 := by
          have r12823 := hand2 (x 5 3) (x 5 13)
          have b12824 := hb (x 5 13)
          have b12825 := hb (x 5 3 && x 5 13)
          clear * - r12823 b12824 b12825 d12810
          omega
        have d12826 : (x 4 1 && x 4 14).toNat = 1 := by
          have r12827 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12828 := hb (x 3 2)
          have b12829 := hb (x 5 13)
          have b12830 := hb (x 4 1 && x 4 14)
          clear * - r12827 b12828 b12829 b12830 d12810 d12243
          omega
        have d12831 : (x 4 1).toNat = 1 := by
          have r12832 := hand1 (x 4 1) (x 4 14)
          have b12833 := hb (x 4 1)
          have b12834 := hb (x 4 1 && x 4 14)
          clear * - r12832 b12833 b12834 d12826
          omega
        have d12835 : (x 5 14).toNat = 0 := by
          have r12836 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12837 := hb (x 4 1)
          have b12838 := hb (x 5 14)
          clear * - r12836 b12837 b12838 d12831
          omega
        have d12839 : (x 5 1 && x 5 14).toNat = 0 := by
          have r12840 := hand2 (x 5 1) (x 5 14)
          have b12841 := hb (x 5 14)
          have b12842 := hb (x 5 1 && x 5 14)
          clear * - r12840 b12841 b12842 d12835
          omega
        have d12843 : (x 5 2).toNat = 0 := by
          have r12844 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b12845 := hb (x 5 2)
          have b12846 := hb (x 5 14)
          clear * - r12844 b12845 b12846 d12835
          omega
        have d12847 : (x 4 2).toNat = 0 := by
          have r12848 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12849 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e12850 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b12851 := hb (x 3 3)
          have b12852 := hb (x 4 2)
          have b12853 := hb (x 5 13)
          have b12854 := hb (x 6 12)
          clear * - r12848 e12849 e12850 b12851 b12852 b12853 b12854 d12794 d12810 d12790
          omega
        have d12855 : (x 6 13).toNat = 1 := by
          have r12856 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12857 := hb (x 4 2)
          have b12858 := hb (x 6 13)
          have b12859 := hb (x 5 1 && x 5 14)
          clear * - r12856 b12857 b12858 b12859 d12839 d12847
          omega
        have d12860 : (x 6 1).toNat = 1 := by
          have r12861 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
          have b12862 := hb (x 6 1)
          have b12863 := hb (x 6 13)
          clear * - r12861 b12862 b12863 d12855
          omega
        have d12864 : (x 7 14).toNat = 0 := by
          have r12865 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12866 := hb (x 6 1)
          have b12867 := hb (x 7 14)
          clear * - r12865 b12866 b12867 d12860
          omega
        have d12868 : (x 7 2).toNat = 0 := by
          have r12869 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b12870 := hb (x 7 2)
          have b12871 := hb (x 7 14)
          clear * - r12869 b12870 b12871 d12864
          omega
        have d12872 : (x 7 12).toNat = 0 := by
          have r12873 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12874 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e12875 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b12876 := hb (x 4 3)
          have b12877 := hb (x 5 2)
          have b12878 := hb (x 6 13)
          have b12879 := hb (x 7 12)
          clear * - r12873 e12874 e12875 b12876 b12877 b12878 b12879 d12855 d12843
          omega
        have d12880 : (x 4 3).toNat = 0 := by
          have r12881 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12882 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e12883 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b12884 := hb (x 4 3)
          have b12885 := hb (x 5 2)
          have b12886 := hb (x 6 13)
          have b12887 := hb (x 7 12)
          clear * - r12881 e12882 e12883 b12884 b12885 b12886 b12887 d12872 d12855 d12843
          omega
        have d12888 : (x 4 3 && x 4 14).toNat = 0 := by
          have r12889 := hand1 (x 4 3) (x 4 14)
          have b12890 := hb (x 4 3)
          have b12891 := hb (x 4 3 && x 4 14)
          clear * - r12889 b12890 b12891 d12880
          omega
        have d12892 : (x 7 11).toNat = 1 := by
          have r12893 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12894 := hb (x 3 4)
          have b12895 := hb (x 7 11)
          have b12896 := hb (x 6 1 && x 6 12)
          have b12897 := hb (x 5 2 && x 5 13)
          have b12898 := hb (x 4 3 && x 4 14)
          clear * - r12893 b12894 b12895 b12896 b12897 b12898 d12802 d12818 d12888 d12271
          omega
        have d12899 : (x 7 3).toNat = 1 := by
          have r12900 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
          have b12901 := hb (x 7 3)
          have b12902 := hb (x 7 11)
          clear * - r12900 b12901 b12902 d12892
          omega
        have d12903 : (x 10 12).toNat = 0 := by
          have r12904 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12905 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e12906 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b12907 := hb (x 7 3)
          have b12908 := hb (x 8 2)
          have b12909 := hb (x 9 13)
          have b12910 := hb (x 10 12)
          clear * - r12904 e12905 e12906 b12907 b12908 b12909 b12910 d12899
          omega
        have d12911 : (x 9 13).toNat = 0 := by
          have r12912 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e12913 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e12914 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b12915 := hb (x 7 3)
          have b12916 := hb (x 8 2)
          have b12917 := hb (x 9 13)
          have b12918 := hb (x 10 12)
          clear * - r12912 e12913 e12914 b12915 b12916 b12917 b12918 d12903 d12899
          omega
        have d12919 : (x 8 1 && x 8 14).toNat = 1 := by
          have r12920 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12921 := hb (x 7 2)
          have b12922 := hb (x 9 13)
          have b12923 := hb (x 8 1 && x 8 14)
          clear * - r12920 b12921 b12922 b12923 d12911 d12868
          omega
        have d12924 : (x 8 14).toNat = 1 := by
          have r12925 := hand2 (x 8 1) (x 8 14)
          have b12926 := hb (x 8 14)
          have b12927 := hb (x 8 1 && x 8 14)
          clear * - r12925 b12926 b12927 d12919
          omega
        have d12928 : (x 7 1).toNat = 0 := by
          have r12929 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12930 := hb (x 7 1)
          have b12931 := hb (x 8 14)
          clear * - r12929 b12930 b12931 d12924
          omega
        have d12932 : (x 7 1 && x 7 11).toNat = 0 := by
          have r12933 := hand1 (x 7 1) (x 7 11)
          have b12934 := hb (x 7 1)
          have b12935 := hb (x 7 1 && x 7 11)
          clear * - r12933 b12934 b12935 d12928
          omega
        have d12936 : (x 8 10).toNat = 1 := by
          have r12937 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b12938 := hb (x 3 5)
          have b12939 := hb (x 8 10)
          have b12940 := hb (x 7 1 && x 7 11)
          have b12941 := hb (x 6 2 && x 6 12)
          have b12942 := hb (x 5 3 && x 5 13)
          have b12943 := hb (x 4 4 && x 4 14)
          clear * - r12937 b12938 b12939 b12940 b12941 b12942 b12943 d12932 d12806 d12822 d12672 d12684
          omega
        have d12944 : (x 8 2).toNat = 1 := by
          have r12945 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
          have b12946 := hb (x 8 2)
          have b12947 := hb (x 8 10)
          clear * - r12945 b12946 b12947 d12936
          omega
        have r12948 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12949 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e12950 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b12951 := hb (x 7 3)
        have b12952 := hb (x 8 2)
        have b12953 := hb (x 9 13)
        have b12954 := hb (x 10 12)
        linarith only [r12948, e12949, e12950, b12951, b12952, b12953, b12954, d12903, d12911, d12944, d12899]
    · have f12955 : (x 0 7).toNat = 1 := by rw [h12285]; rfl
      have d12956 : (x 7 8).toNat = 0 := by
        have r12957 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12958 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e12959 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e12960 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e12961 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e12962 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e12963 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b12964 := hb (x 0 7)
        have b12965 := hb (x 1 6)
        have b12966 := hb (x 2 5)
        have b12967 := hb (x 3 4)
        have b12968 := hb (x 4 11)
        have b12969 := hb (x 5 10)
        have b12970 := hb (x 6 9)
        have b12971 := hb (x 7 8)
        clear * - r12957 e12958 e12959 e12960 e12961 e12962 e12963 b12964 b12965 b12966 b12967 b12968 b12969 b12970 b12971 d12271 g14 f12955
        omega
      have d12972 : (x 6 9).toNat = 0 := by
        have r12973 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12974 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e12975 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e12976 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e12977 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e12978 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e12979 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b12980 := hb (x 0 7)
        have b12981 := hb (x 1 6)
        have b12982 := hb (x 2 5)
        have b12983 := hb (x 3 4)
        have b12984 := hb (x 4 11)
        have b12985 := hb (x 5 10)
        have b12986 := hb (x 6 9)
        have b12987 := hb (x 7 8)
        clear * - r12973 e12974 e12975 e12976 e12977 e12978 e12979 b12980 b12981 b12982 b12983 b12984 b12985 b12986 b12987 d12956 d12271 g14 f12955
        omega
      have d12988 : (x 5 10).toNat = 0 := by
        have r12989 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e12990 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e12991 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e12992 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e12993 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e12994 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e12995 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b12996 := hb (x 0 7)
        have b12997 := hb (x 1 6)
        have b12998 := hb (x 2 5)
        have b12999 := hb (x 3 4)
        have b13000 := hb (x 4 11)
        have b13001 := hb (x 5 10)
        have b13002 := hb (x 6 9)
        have b13003 := hb (x 7 8)
        clear * - r12989 e12990 e12991 e12992 e12993 e12994 e12995 b12996 b12997 b12998 b12999 b13000 b13001 b13002 b13003 d12956 d12972 d12271 g14 f12955
        omega
      have d13004 : (x 5 1 && x 5 10).toNat = 0 := by
        have r13005 := hand2 (x 5 1) (x 5 10)
        have b13006 := hb (x 5 10)
        have b13007 := hb (x 5 1 && x 5 10)
        clear * - r13005 b13006 b13007 d12988
        omega
      have d13008 : (x 4 11).toNat = 0 := by
        have r13009 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13010 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e13011 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e13012 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e13013 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e13014 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e13015 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b13016 := hb (x 0 7)
        have b13017 := hb (x 1 6)
        have b13018 := hb (x 2 5)
        have b13019 := hb (x 3 4)
        have b13020 := hb (x 4 11)
        have b13021 := hb (x 5 10)
        have b13022 := hb (x 6 9)
        have b13023 := hb (x 7 8)
        clear * - r13009 e13010 e13011 e13012 e13013 e13014 e13015 b13016 b13017 b13018 b13019 b13020 b13021 b13022 b13023 d12956 d12972 d12988 d12271 g14 f12955
        omega
      have d13024 : (x 4 1 && x 4 11).toNat = 0 := by
        have r13025 := hand2 (x 4 1) (x 4 11)
        have b13026 := hb (x 4 11)
        have b13027 := hb (x 4 1 && x 4 11)
        clear * - r13025 b13026 b13027 d13008
        omega
      have d13028 : (x 2 3 && x 2 13).toNat = 1 := by
        have r13029 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13030 := hb (x 0 5)
        have b13031 := hb (x 5 10)
        have b13032 := hb (x 4 1 && x 4 11)
        have b13033 := hb (x 3 2 && x 3 12)
        have b13034 := hb (x 2 3 && x 2 13)
        have b13035 := hb (x 1 4 && x 1 14)
        clear * - r13029 b13030 b13031 b13032 b13033 b13034 b13035 d12988 d13024 d12247 g48 g10
        omega
      have d13036 : (x 2 3).toNat = 1 := by
        have r13037 := hand1 (x 2 3) (x 2 13)
        have b13038 := hb (x 2 3)
        have b13039 := hb (x 2 3 && x 2 13)
        clear * - r13037 b13038 b13039 d13028
        omega
      have d13040 : (x 5 12).toNat = 0 := by
        have r13041 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13042 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e13043 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b13044 := hb (x 2 3)
        have b13045 := hb (x 3 2)
        have b13046 := hb (x 4 13)
        have b13047 := hb (x 5 12)
        clear * - r13041 e13042 e13043 b13044 b13045 b13046 b13047 d12243 d13036
        omega
      have d13048 : (x 4 13).toNat = 0 := by
        have r13049 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13050 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e13051 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b13052 := hb (x 2 3)
        have b13053 := hb (x 3 2)
        have b13054 := hb (x 4 13)
        have b13055 := hb (x 5 12)
        clear * - r13049 e13050 e13051 b13052 b13053 b13054 b13055 d13040 d12243 d13036
        omega
      have d13056 : (x 2 2).toNat = 1 := by
        have r13057 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13058 := hb (x 2 2)
        have b13059 := hb (x 4 13)
        have b13060 := hb (x 3 1 && x 3 14)
        clear * - r13057 b13058 b13059 b13060 d13048 d12231
        omega
      have d13061 : (x 2 14).toNat = 1 := by
        have r13062 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
        have b13063 := hb (x 2 2)
        have b13064 := hb (x 2 14)
        clear * - r13062 b13063 b13064 d13056
        omega
      have d13065 : (x 1 1).toNat = 0 := by
        have r13066 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13067 := hb (x 1 1)
        have b13068 := hb (x 2 14)
        clear * - r13066 b13067 b13068 d13061
        omega
      have d13069 : (x 1 13).toNat = 0 := by
        have r13070 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
        have b13071 := hb (x 1 1)
        have b13072 := hb (x 1 13)
        clear * - r13070 b13071 b13072 d13065
        omega
      have d13073 : (x 4 12).toNat = 0 := by
        have r13074 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13075 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e13076 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b13077 := hb (x 1 3)
        have b13078 := hb (x 2 2)
        have b13079 := hb (x 3 13)
        have b13080 := hb (x 4 12)
        clear * - r13074 e13075 e13076 b13077 b13078 b13079 b13080 d13056
        omega
      have d13081 : (x 4 3 && x 4 12).toNat = 0 := by
        have r13082 := hand2 (x 4 3) (x 4 12)
        have b13083 := hb (x 4 12)
        have b13084 := hb (x 4 3 && x 4 12)
        clear * - r13082 b13083 b13084 d13073
        omega
      have d13085 : (x 4 4).toNat = 0 := by
        have r13086 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b13087 := hb (x 4 4)
        have b13088 := hb (x 4 12)
        clear * - r13086 b13087 b13088 d13073
        omega
      have d13089 : (x 3 13).toNat = 0 := by
        have r13090 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13091 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e13092 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b13093 := hb (x 1 3)
        have b13094 := hb (x 2 2)
        have b13095 := hb (x 3 13)
        have b13096 := hb (x 4 12)
        clear * - r13090 e13091 e13092 b13093 b13094 b13095 b13096 d13073 d13056
        omega
      have d13097 : (x 3 5).toNat = 0 := by
        have r13098 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
        have b13099 := hb (x 3 5)
        have b13100 := hb (x 3 13)
        clear * - r13098 b13099 b13100 d13089
        omega
      have d13101 : (x 1 3).toNat = 0 := by
        have r13102 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13103 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e13104 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b13105 := hb (x 1 3)
        have b13106 := hb (x 2 2)
        have b13107 := hb (x 3 13)
        have b13108 := hb (x 4 12)
        clear * - r13102 e13103 e13104 b13105 b13106 b13107 b13108 d13073 d13089 d13056
        omega
      have d13109 : (x 1 3 && x 1 7).toNat = 0 := by
        have r13110 := hand1 (x 1 3) (x 1 7)
        have b13111 := hb (x 1 3)
        have b13112 := hb (x 1 3 && x 1 7)
        clear * - r13110 b13111 b13112 d13101
        omega
      have d13113 : (x 4 2 && x 4 11).toNat = 0 := by
        have r13114 := hand2 (x 4 2) (x 4 11)
        have b13115 := hb (x 4 11)
        have b13116 := hb (x 4 2 && x 4 11)
        clear * - r13114 b13115 b13116 d13008
        omega
      have d13117 : (x 2 4 && x 2 13).toNat = 1 := by
        have r13118 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b13119 := hb (x 0 6)
        have b13120 := hb (x 6 9)
        have b13121 := hb (x 5 1 && x 5 10)
        have b13122 := hb (x 4 2 && x 4 11)
        have b13123 := hb (x 3 3 && x 3 12)
        have b13124 := hb (x 2 4 && x 2 13)
        have b13125 := hb (x 1 5 && x 1 14)
        clear * - r13118 b13119 b13120 b13121 b13122 b13123 b13124 b13125 d12972 d13004 d13113 d12267 g40 f12280
        omega
      have d13126 : (x 2 4).toNat = 1 := by
        have r13127 := hand1 (x 2 4) (x 2 13)
        have b13128 := hb (x 2 4)
        have b13129 := hb (x 2 4 && x 2 13)
        clear * - r13127 b13128 b13129 d13117
        omega
      have d13130 : (x 2 12).toNat = 1 := by
        have r13131 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
        have b13132 := hb (x 2 4)
        have b13133 := hb (x 2 12)
        clear * - r13131 b13132 b13133 d13126
        omega
      have d13134 : (x (-1) 3).toNat = 0 := by
        have r13135 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13136 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e13137 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b13138 := hb (x (-1) 3)
        have b13139 := hb (x 0 2)
        have b13140 := hb (x 1 13)
        have b13141 := hb (x 2 12)
        clear * - r13135 e13136 e13137 b13138 b13139 b13140 b13141 d13130 d13069 g7
        omega
      have d13142 : (x (-1) 11).toNat = 0 := by
        have r13143 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
        have b13144 := hb (x (-1) 3)
        have b13145 := hb (x (-1) 11)
        clear * - r13143 b13144 b13145 d13134
        omega
      have d13146 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
        have r13147 := hand2 (x (-1) 1) (x (-1) 11)
        have b13148 := hb (x (-1) 11)
        have b13149 := hb (x (-1) 1 && x (-1) 11)
        clear * - r13147 b13148 b13149 d13142
        omega
      have d13150 : (x 2 5).toNat = 0 := by
        have r13151 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e13152 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e13153 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e13154 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e13155 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e13156 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e13157 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b13158 := hb (x 0 7)
        have b13159 := hb (x 1 6)
        have b13160 := hb (x 2 5)
        have b13161 := hb (x 3 4)
        have b13162 := hb (x 4 11)
        have b13163 := hb (x 5 10)
        have b13164 := hb (x 6 9)
        have b13165 := hb (x 7 8)
        clear * - r13151 e13152 e13153 e13154 e13155 e13156 e13157 b13158 b13159 b13160 b13161 b13162 b13163 b13164 b13165 d12956 d12972 d12988 d13008 d12271 g14 f12955
        omega
      have d13166 : (x 2 5 && x 2 14).toNat = 0 := by
        have r13167 := hand1 (x 2 5) (x 2 14)
        have b13168 := hb (x 2 5)
        have b13169 := hb (x 2 5 && x 2 14)
        clear * - r13167 b13168 b13169 d13150
        omega
      have r13170 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r13171 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13172 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e13173 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e13174 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e13175 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e13176 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e13177 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have r13178 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13179 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e13180 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e13181 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e13182 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e13183 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e13184 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have r13185 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13186 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e13187 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have r13188 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13189 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e13190 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have r13191 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13192 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e13193 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have r13194 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r13195 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r13196 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13197 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
      have e13198 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
      have r13199 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r13200 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r13201 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r13202 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r13203 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r13204 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r13205 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r13206 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
      have r13207 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have r13208 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
      have r13209 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
      have r13210 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
      have r13211 := hand2 (x 2 2) (x 2 6)
      have r13212 := hand2 (x 0 4) (x 0 8)
      have r13213 := hand1 (x (-4) 8) (x (-4) 12)
      have r13214 := hand1 (x (-5) 9) (x (-5) 13)
      have r13215 := hand2 (x 6 1) (x 6 10)
      have r13216 := hand2 (x 5 2) (x 5 11)
      have r13217 := hand2 (x (-4) 4) (x (-4) 14)
      have r13218 := hand1 (x (-2) 4) (x (-2) 14)
      have r13219 := hand1 (x (-5) 1) (x (-5) 12)
      have r13220 := hand1 (x (-6) 2) (x (-6) 13)
      have r13221 := hand1 (x (-7) 3) (x (-7) 14)
      have r13222 := hand2 (x (-1) 1) (x (-1) 12)
      have r13223 := hand1 (x (-3) 1) (x (-3) 14)
      have r13224 := hand2 (x (-2) 1) (x (-2) 14)
      linarith only [r13170, r13171, e13172, e13173, e13174, e13175, e13176, e13177, r13178, e13179, e13180, e13181, e13182, e13183, e13184, r13185, e13186, e13187, r13188, e13189, e13190, r13191, e13192, e13193, r13194, r13195, r13196, e13197, e13198, r13199, r13200, r13201, r13202, r13203, r13204, r13205, r13206, r13207, r13208, r13209, r13210, r13211, r13212, r13213, r13214, r13215, r13216, r13217, r13218, r13219, r13220, r13221, r13222, r13223, r13224, g0, g1, g3, g4, g5, g6, g9, g11, g12, d13101, g14, d13056, g16, d13097, d13085, d13109, g18, g19, g20, d13081, d12275, d13166, d13146, g42, g43, g44, d12210, g45, g49, g50]
  · have f13309 : (x 0 6).toNat = 1 := by rw [h12279]; rfl
    have d13310 : (x 0 14).toNat = 1 := by
      have r13311 : (x 0 6).toNat ≤ (x 0 14).toNat := himp _ _ (hp6 0)
      have b13312 := hb (x 0 6)
      have b13313 := hb (x 0 14)
      clear * - r13311 b13312 b13313 f13309
      omega
    have d13314 : (x (-1) 1).toNat = 0 := by
      have r13315 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13316 := hb (x (-1) 1)
      have b13317 := hb (x 0 14)
      clear * - r13315 b13316 b13317 d13310
      omega
    have d13318 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
      have r13319 := hand1 (x (-1) 1) (x (-1) 14)
      have b13320 := hb (x (-1) 1)
      have b13321 := hb (x (-1) 1 && x (-1) 14)
      clear * - r13319 b13320 b13321 d13314
      omega
    have d13322 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
      have r13323 := hand1 (x (-1) 1) (x (-1) 12)
      have b13324 := hb (x (-1) 1)
      have b13325 := hb (x (-1) 1 && x (-1) 12)
      clear * - r13323 b13324 b13325 d13314
      omega
    have d13326 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
      have r13327 := hand1 (x (-1) 1) (x (-1) 11)
      have b13328 := hb (x (-1) 1)
      have b13329 := hb (x (-1) 1 && x (-1) 11)
      clear * - r13327 b13328 b13329 d13314
      omega
    have d13330 : (x 0 13).toNat = 1 := by
      have r13331 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13332 := hb (x (-2) 2)
      have b13333 := hb (x 0 13)
      have b13334 := hb (x (-1) 1 && x (-1) 14)
      clear * - r13331 b13332 b13333 b13334 d13318 g2
      omega
    have d13335 : (x 1 12).toNat = 0 := by
      have r13336 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13337 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e13338 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b13339 := hb (x (-2) 3)
      have b13340 := hb (x (-1) 2)
      have b13341 := hb (x 0 13)
      have b13342 := hb (x 1 12)
      clear * - r13336 e13337 e13338 b13339 b13340 b13341 b13342 d13330
      omega
    have d13343 : (x 1 4).toNat = 0 := by
      have r13344 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
      have b13345 := hb (x 1 4)
      have b13346 := hb (x 1 12)
      clear * - r13344 b13345 b13346 d13335
      omega
    have d13347 : (x 1 4 && x 1 13).toNat = 0 := by
      have r13348 := hand1 (x 1 4) (x 1 13)
      have b13349 := hb (x 1 4)
      have b13350 := hb (x 1 4 && x 1 13)
      clear * - r13348 b13349 b13350 d13343
      omega
    have d13351 : (x (-1) 2).toNat = 0 := by
      have r13352 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13353 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e13354 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b13355 := hb (x (-2) 3)
      have b13356 := hb (x (-1) 2)
      have b13357 := hb (x 0 13)
      have b13358 := hb (x 1 12)
      clear * - r13352 e13353 e13354 b13355 b13356 b13357 b13358 d13335 d13330
      omega
    have d13359 : (x (-1) 10).toNat = 0 := by
      have r13360 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
      have b13361 := hb (x (-1) 2)
      have b13362 := hb (x (-1) 10)
      clear * - r13360 b13361 b13362 d13351
      omega
    have d13363 : (x (-1) 3 && x (-1) 10).toNat = 0 := by
      have r13364 := hand2 (x (-1) 3) (x (-1) 10)
      have b13365 := hb (x (-1) 10)
      have b13366 := hb (x (-1) 3 && x (-1) 10)
      clear * - r13364 b13365 b13366 d13359
      omega
    have d13367 : (x (-2) 3).toNat = 0 := by
      have r13368 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13369 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e13370 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b13371 := hb (x (-2) 3)
      have b13372 := hb (x (-1) 2)
      have b13373 := hb (x 0 13)
      have b13374 := hb (x 1 12)
      clear * - r13368 e13369 e13370 b13371 b13372 b13373 b13374 d13335 d13330 d13351
      omega
    have d13375 : (x (-2) 11).toNat = 0 := by
      have r13376 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
      have b13377 := hb (x (-2) 3)
      have b13378 := hb (x (-2) 11)
      clear * - r13376 b13377 b13378 d13367
      omega
    have d13379 : (x (-2) 4 && x (-2) 11).toNat = 0 := by
      have r13380 := hand2 (x (-2) 4) (x (-2) 11)
      have b13381 := hb (x (-2) 11)
      have b13382 := hb (x (-2) 4 && x (-2) 11)
      clear * - r13380 b13381 b13382 d13375
      omega
    have d13383 : (x (-4) 4).toNat = 1 := by
      have r13384 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13385 := hb (x (-4) 4)
      have b13386 := hb (x 0 11)
      have b13387 := hb (x (-1) 1 && x (-1) 12)
      have b13388 := hb (x (-2) 2 && x (-2) 13)
      have b13389 := hb (x (-3) 3 && x (-3) 14)
      clear * - r13384 b13385 b13386 b13387 b13388 b13389 g12 d13322 g49 g50
      omega
    have d13390 : (x (-4) 12).toNat = 1 := by
      have r13391 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
      have b13392 := hb (x (-4) 4)
      have b13393 := hb (x (-4) 12)
      clear * - r13391 b13392 b13393 d13383
      omega
    have d13394 : (x (-5) 13).toNat = 0 := by
      have r13395 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13396 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e13397 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b13398 := hb (x (-7) 3)
      have b13399 := hb (x (-6) 2)
      have b13400 := hb (x (-5) 13)
      have b13401 := hb (x (-4) 12)
      clear * - r13395 e13396 e13397 b13398 b13399 b13400 b13401 d13390
      omega
    have d13402 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
      have r13403 := hand2 (x (-5) 3) (x (-5) 13)
      have b13404 := hb (x (-5) 13)
      have b13405 := hb (x (-5) 3 && x (-5) 13)
      clear * - r13403 b13404 b13405 d13394
      omega
    have d13406 : (x (-5) 5).toNat = 0 := by
      have r13407 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
      have b13408 := hb (x (-5) 5)
      have b13409 := hb (x (-5) 13)
      clear * - r13407 b13408 b13409 d13394
      omega
    have d13410 : (x (-6) 2).toNat = 0 := by
      have r13411 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13412 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e13413 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have b13414 := hb (x (-7) 3)
      have b13415 := hb (x (-6) 2)
      have b13416 := hb (x (-5) 13)
      have b13417 := hb (x (-4) 12)
      clear * - r13411 e13412 e13413 b13414 b13415 b13416 b13417 d13390 d13394
      omega
    have d13418 : (x (-4) 4 && x (-4) 14).toNat = 1 := by
      have r13419 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13420 := hb (x (-5) 5)
      have b13421 := hb (x 0 10)
      have b13422 := hb (x (-1) 1 && x (-1) 11)
      have b13423 := hb (x (-2) 2 && x (-2) 12)
      have b13424 := hb (x (-3) 3 && x (-3) 13)
      have b13425 := hb (x (-4) 4 && x (-4) 14)
      clear * - r13419 b13420 b13421 b13422 b13423 b13424 b13425 g11 d13326 g42 g43 d13406
      omega
    have d13426 : (x (-4) 14).toNat = 1 := by
      have r13427 := hand2 (x (-4) 4) (x (-4) 14)
      have b13428 := hb (x (-4) 14)
      have b13429 := hb (x (-4) 4 && x (-4) 14)
      clear * - r13427 b13428 b13429 d13418
      omega
    have d13430 : (x (-5) 1).toNat = 0 := by
      have r13431 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13432 := hb (x (-5) 1)
      have b13433 := hb (x (-4) 14)
      clear * - r13431 b13432 b13433 d13426
      omega
    have d13434 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
      have r13435 := hand1 (x (-5) 1) (x (-5) 14)
      have b13436 := hb (x (-5) 1)
      have b13437 := hb (x (-5) 1 && x (-5) 14)
      clear * - r13435 b13436 b13437 d13430
      omega
    have d13438 : (x (-4) 13).toNat = 1 := by
      have r13439 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13440 := hb (x (-6) 2)
      have b13441 := hb (x (-4) 13)
      have b13442 := hb (x (-5) 1 && x (-5) 14)
      clear * - r13439 b13440 b13441 b13442 d13434 d13410
      omega
    have d13443 : (x (-4) 1).toNat = 1 := by
      have r13444 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
      have b13445 := hb (x (-4) 1)
      have b13446 := hb (x (-4) 13)
      clear * - r13444 b13445 b13446 d13438
      omega
    have d13447 : (x (-3) 14).toNat = 0 := by
      have r13448 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13449 := hb (x (-4) 1)
      have b13450 := hb (x (-3) 14)
      clear * - r13448 b13449 b13450 d13443
      omega
    have d13451 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
      have r13452 := hand2 (x (-3) 1) (x (-3) 14)
      have b13453 := hb (x (-3) 14)
      have b13454 := hb (x (-3) 1 && x (-3) 14)
      clear * - r13452 b13453 b13454 d13447
      omega
    have d13455 : (x (-3) 2).toNat = 0 := by
      have r13456 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b13457 := hb (x (-3) 2)
      have b13458 := hb (x (-3) 14)
      clear * - r13456 b13457 b13458 d13447
      omega
    have d13459 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
      have r13460 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13461 := hb (x (-3) 2)
      have b13462 := hb (x (-1) 13)
      have b13463 := hb (x (-2) 1 && x (-2) 14)
      clear * - r13460 b13461 b13462 b13463 g6 d13455
      omega
    have d13464 : (x (-2) 14).toNat = 1 := by
      have r13465 := hand2 (x (-2) 1) (x (-2) 14)
      have b13466 := hb (x (-2) 14)
      have b13467 := hb (x (-2) 1 && x (-2) 14)
      clear * - r13465 b13466 b13467 d13459
      omega
    have d13468 : (x (-3) 1).toNat = 0 := by
      have r13469 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13470 := hb (x (-3) 1)
      have b13471 := hb (x (-2) 14)
      clear * - r13469 b13470 b13471 d13464
      omega
    have d13472 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
      have r13473 := hand1 (x (-3) 1) (x (-3) 12)
      have b13474 := hb (x (-3) 1)
      have b13475 := hb (x (-3) 1 && x (-3) 12)
      clear * - r13473 b13474 b13475 d13468
      omega
    have d13476 : (x (-3) 13).toNat = 0 := by
      have r13477 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
      have b13478 := hb (x (-3) 1)
      have b13479 := hb (x (-3) 13)
      clear * - r13477 b13478 b13479 d13468
      omega
    have d13480 : (x (-3) 5).toNat = 0 := by
      have r13481 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
      have b13482 := hb (x (-3) 5)
      have b13483 := hb (x (-3) 13)
      clear * - r13481 b13482 b13483 d13476
      omega
    have d13484 : (x (-3) 5 && x (-3) 12).toNat = 0 := by
      have r13485 := hand1 (x (-3) 5) (x (-3) 12)
      have b13486 := hb (x (-3) 5)
      have b13487 := hb (x (-3) 5 && x (-3) 12)
      clear * - r13485 b13486 b13487 d13480
      omega
    have d13488 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
      have r13489 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13490 := hb (x (-3) 5)
      have b13491 := hb (x 2 10)
      have b13492 := hb (x 1 1 && x 1 11)
      have b13493 := hb (x 0 2 && x 0 12)
      have b13494 := hb (x (-1) 3 && x (-1) 13)
      have b13495 := hb (x (-2) 4 && x (-2) 14)
      clear * - r13489 b13490 b13491 b13492 b13493 b13494 b13495 g16 g44 d12210 g45 d13480
      omega
    have d13496 : (x (-2) 4).toNat = 1 := by
      have r13497 := hand1 (x (-2) 4) (x (-2) 14)
      have b13498 := hb (x (-2) 4)
      have b13499 := hb (x (-2) 4 && x (-2) 14)
      clear * - r13497 b13498 b13499 d13488
      omega
    have d13500 : (x (-2) 12).toNat = 1 := by
      have r13501 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
      have b13502 := hb (x (-2) 4)
      have b13503 := hb (x (-2) 12)
      clear * - r13501 b13502 b13503 d13496
      omega
    have d13504 : (x (-4) 2).toNat = 0 := by
      have r13505 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13506 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e13507 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b13508 := hb (x (-5) 3)
      have b13509 := hb (x (-4) 2)
      have b13510 := hb (x (-3) 13)
      have b13511 := hb (x (-2) 12)
      clear * - r13505 e13506 e13507 b13508 b13509 b13510 b13511 d13500 d13476
      omega
    have d13512 : (x (-4) 2 && x (-4) 13).toNat = 0 := by
      have r13513 := hand1 (x (-4) 2) (x (-4) 13)
      have b13514 := hb (x (-4) 2)
      have b13515 := hb (x (-4) 2 && x (-4) 13)
      clear * - r13513 b13514 b13515 d13504
      omega
    have d13516 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
      have r13517 := hand1 (x (-4) 2) (x (-4) 12)
      have b13518 := hb (x (-4) 2)
      have b13519 := hb (x (-4) 2 && x (-4) 12)
      clear * - r13517 b13518 b13519 d13504
      omega
    have d13520 : (x (-2) 13).toNat = 1 := by
      have r13521 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13522 := hb (x (-4) 2)
      have b13523 := hb (x (-2) 13)
      have b13524 := hb (x (-3) 1 && x (-3) 14)
      clear * - r13521 b13522 b13523 b13524 d13451 d13504
      omega
    have d13525 : (x (-2) 1).toNat = 1 := by
      have r13526 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
      have b13527 := hb (x (-2) 1)
      have b13528 := hb (x (-2) 13)
      clear * - r13526 b13527 b13528 d13520
      omega
    have d13529 : (x (-1) 14).toNat = 0 := by
      have r13530 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13531 := hb (x (-2) 1)
      have b13532 := hb (x (-1) 14)
      clear * - r13530 b13531 b13532 d13525
      omega
    have d13533 : (x (-1) 6).toNat = 0 := by
      have r13534 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
      have b13535 := hb (x (-1) 6)
      have b13536 := hb (x (-1) 14)
      clear * - r13534 b13535 b13536 d13529
      omega
    have d13537 : (x (-5) 3).toNat = 0 := by
      have r13538 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13539 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e13540 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b13541 := hb (x (-5) 3)
      have b13542 := hb (x (-4) 2)
      have b13543 := hb (x (-3) 13)
      have b13544 := hb (x (-2) 12)
      clear * - r13538 e13539 e13540 b13541 b13542 b13543 b13544 d13500 d13476 d13504
      omega
    have d13545 : (x (-5) 3 && x (-5) 14).toNat = 0 := by
      have r13546 := hand1 (x (-5) 3) (x (-5) 14)
      have b13547 := hb (x (-5) 3)
      have b13548 := hb (x (-5) 3 && x (-5) 14)
      clear * - r13546 b13547 b13548 d13537
      omega
    have d13549 : (x (-6) 4).toNat = 1 := by
      have r13550 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13551 := hb (x (-6) 4)
      have b13552 := hb (x (-2) 11)
      have b13553 := hb (x (-3) 1 && x (-3) 12)
      have b13554 := hb (x (-4) 2 && x (-4) 13)
      have b13555 := hb (x (-5) 3 && x (-5) 14)
      clear * - r13550 b13551 b13552 b13553 b13554 b13555 d13375 d13472 d13512 d13545
      omega
    have d13556 : (x (-6) 12).toNat = 1 := by
      have r13557 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
      have b13558 := hb (x (-6) 4)
      have b13559 := hb (x (-6) 12)
      clear * - r13557 b13558 b13559 d13549
      omega
    have d13560 : (x (-7) 13).toNat = 0 := by
      have r13561 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13562 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e13563 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b13564 := hb (x (-9) 3)
      have b13565 := hb (x (-8) 2)
      have b13566 := hb (x (-7) 13)
      have b13567 := hb (x (-6) 12)
      clear * - r13561 e13562 e13563 b13564 b13565 b13566 b13567 d13556
      omega
    have d13568 : (x (-7) 5).toNat = 0 := by
      have r13569 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
      have b13570 := hb (x (-7) 5)
      have b13571 := hb (x (-7) 13)
      clear * - r13569 b13570 b13571 d13560
      omega
    have d13572 : (x (-8) 2).toNat = 0 := by
      have r13573 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13574 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e13575 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b13576 := hb (x (-9) 3)
      have b13577 := hb (x (-8) 2)
      have b13578 := hb (x (-7) 13)
      have b13579 := hb (x (-6) 12)
      clear * - r13573 e13574 e13575 b13576 b13577 b13578 b13579 d13556 d13560
      omega
    have d13580 : (x (-8) 2 && x (-8) 13).toNat = 0 := by
      have r13581 := hand1 (x (-8) 2) (x (-8) 13)
      have b13582 := hb (x (-8) 2)
      have b13583 := hb (x (-8) 2 && x (-8) 13)
      clear * - r13581 b13582 b13583 d13572
      omega
    have d13584 : (x (-8) 10).toNat = 0 := by
      have r13585 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
      have b13586 := hb (x (-8) 2)
      have b13587 := hb (x (-8) 10)
      clear * - r13585 b13586 b13587 d13572
      omega
    have d13588 : (x (-9) 3).toNat = 0 := by
      have r13589 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13590 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e13591 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have b13592 := hb (x (-9) 3)
      have b13593 := hb (x (-8) 2)
      have b13594 := hb (x (-7) 13)
      have b13595 := hb (x (-6) 12)
      clear * - r13589 e13590 e13591 b13592 b13593 b13594 b13595 d13556 d13560 d13572
      omega
    have d13596 : (x (-9) 3 && x (-9) 14).toNat = 0 := by
      have r13597 := hand1 (x (-9) 3) (x (-9) 14)
      have b13598 := hb (x (-9) 3)
      have b13599 := hb (x (-9) 3 && x (-9) 14)
      clear * - r13597 b13598 b13599 d13588
      omega
    have d13600 : (x (-9) 11).toNat = 0 := by
      have r13601 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
      have b13602 := hb (x (-9) 3)
      have b13603 := hb (x (-9) 11)
      clear * - r13601 b13602 b13603 d13588
      omega
    have d13604 : (x (-3) 12).toNat = 0 := by
      have r13605 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13606 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e13607 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b13608 := hb (x (-6) 3)
      have b13609 := hb (x (-5) 2)
      have b13610 := hb (x (-4) 13)
      have b13611 := hb (x (-3) 12)
      clear * - r13605 e13606 e13607 b13608 b13609 b13610 b13611 d13438
      omega
    have d13612 : (x (-5) 2).toNat = 0 := by
      have r13613 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13614 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e13615 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b13616 := hb (x (-6) 3)
      have b13617 := hb (x (-5) 2)
      have b13618 := hb (x (-4) 13)
      have b13619 := hb (x (-3) 12)
      clear * - r13613 e13614 e13615 b13616 b13617 b13618 b13619 d13604 d13438
      omega
    have d13620 : (x (-6) 3).toNat = 0 := by
      have r13621 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13622 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e13623 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b13624 := hb (x (-6) 3)
      have b13625 := hb (x (-5) 2)
      have b13626 := hb (x (-4) 13)
      have b13627 := hb (x (-3) 12)
      clear * - r13621 e13622 e13623 b13624 b13625 b13626 b13627 d13604 d13438 d13612
      omega
    have d13628 : (x (-6) 11).toNat = 0 := by
      have r13629 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
      have b13630 := hb (x (-6) 3)
      have b13631 := hb (x (-6) 11)
      clear * - r13629 b13630 b13631 d13620
      omega
    have d13632 : (x (-6) 4 && x (-6) 14).toNat = 1 := by
      have r13633 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13634 := hb (x (-7) 5)
      have b13635 := hb (x (-2) 10)
      have b13636 := hb (x (-3) 1 && x (-3) 11)
      have b13637 := hb (x (-4) 2 && x (-4) 12)
      have b13638 := hb (x (-5) 3 && x (-5) 13)
      have b13639 := hb (x (-6) 4 && x (-6) 14)
      clear * - r13633 b13634 b13635 b13636 b13637 b13638 b13639 g4 g41 d13516 d13402 d13568
      omega
    have d13640 : (x (-6) 14).toNat = 1 := by
      have r13641 := hand2 (x (-6) 4) (x (-6) 14)
      have b13642 := hb (x (-6) 14)
      have b13643 := hb (x (-6) 4 && x (-6) 14)
      clear * - r13641 b13642 b13643 d13632
      omega
    have d13644 : (x (-7) 1).toNat = 0 := by
      have r13645 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13646 := hb (x (-7) 1)
      have b13647 := hb (x (-6) 14)
      clear * - r13645 b13646 b13647 d13640
      omega
    have d13648 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
      have r13649 := hand1 (x (-7) 1) (x (-7) 14)
      have b13650 := hb (x (-7) 1)
      have b13651 := hb (x (-7) 1 && x (-7) 14)
      clear * - r13649 b13650 b13651 d13644
      omega
    have d13652 : (x (-6) 13).toNat = 1 := by
      have r13653 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13654 := hb (x (-8) 2)
      have b13655 := hb (x (-6) 13)
      have b13656 := hb (x (-7) 1 && x (-7) 14)
      clear * - r13653 b13654 b13655 b13656 d13648 d13572
      omega
    have d13657 : (x (-6) 1).toNat = 1 := by
      have r13658 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
      have b13659 := hb (x (-6) 1)
      have b13660 := hb (x (-6) 13)
      clear * - r13658 b13659 b13660 d13652
      omega
    have d13661 : (x (-5) 14).toNat = 0 := by
      have r13662 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13663 := hb (x (-6) 1)
      have b13664 := hb (x (-5) 14)
      clear * - r13662 b13663 b13664 d13657
      omega
    have d13665 : (x (-5) 7 && x (-5) 14).toNat = 0 := by
      have r13666 := hand2 (x (-5) 7) (x (-5) 14)
      have b13667 := hb (x (-5) 14)
      have b13668 := hb (x (-5) 7 && x (-5) 14)
      clear * - r13666 b13667 b13668 d13661
      omega
    have d13669 : (x (-7) 1 && x (-7) 12).toNat = 0 := by
      have r13670 := hand1 (x (-7) 1) (x (-7) 12)
      have b13671 := hb (x (-7) 1)
      have b13672 := hb (x (-7) 1 && x (-7) 12)
      clear * - r13670 b13671 b13672 d13644
      omega
    have d13673 : (x (-10) 4).toNat = 1 := by
      have r13674 : 1 ≤ (x (-6) 11).toNat + (x (-7) 1 && x (-7) 12).toNat + (x (-8) 2 && x (-8) 13).toNat + (x (-9) 3 && x (-9) 14).toNat + (x (-10) 4).toNat := by have q := hcov11 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13675 := hb (x (-10) 4)
      have b13676 := hb (x (-6) 11)
      have b13677 := hb (x (-7) 1 && x (-7) 12)
      have b13678 := hb (x (-8) 2 && x (-8) 13)
      have b13679 := hb (x (-9) 3 && x (-9) 14)
      clear * - r13674 b13675 b13676 b13677 b13678 b13679 d13628 d13669 d13580 d13596
      omega
    have d13680 : (x (-10) 12).toNat = 1 := by
      have r13681 : (x (-10) 4).toNat ≤ (x (-10) 12).toNat := himp _ _ (hp4 (-10))
      have b13682 := hb (x (-10) 4)
      have b13683 := hb (x (-10) 12)
      clear * - r13681 b13682 b13683 d13673
      omega
    have d13684 : (x (-11) 13).toNat = 0 := by
      have r13685 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13686 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
      have e13687 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
      have b13688 := hb (x (-13) 3)
      have b13689 := hb (x (-12) 2)
      have b13690 := hb (x (-11) 13)
      have b13691 := hb (x (-10) 12)
      clear * - r13685 e13686 e13687 b13688 b13689 b13690 b13691 d13680
      omega
    have d13692 : (x (-11) 5).toNat = 0 := by
      have r13693 : (x (-11) 5).toNat ≤ (x (-11) 13).toNat := himp _ _ (hp5 (-11))
      have b13694 := hb (x (-11) 5)
      have b13695 := hb (x (-11) 13)
      clear * - r13693 b13694 b13695 d13684
      omega
    have d13696 : (x (-7) 9).toNat = 0 := by
      have r13697 : (x (-7) 9).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp9 (-7))
      have b13698 := hb (x (-7) 1)
      have b13699 := hb (x (-7) 9)
      clear * - r13697 b13698 b13699 d13644
      omega
    have d13700 : (x 6 8).toNat = 0 := by
      have r13701 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13702 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e13703 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e13704 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e13705 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e13706 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e13707 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b13708 := hb (x (-1) 7)
      have b13709 := hb (x 0 6)
      have b13710 := hb (x 1 5)
      have b13711 := hb (x 2 4)
      have b13712 := hb (x 3 11)
      have b13713 := hb (x 4 10)
      have b13714 := hb (x 5 9)
      have b13715 := hb (x 6 8)
      clear * - r13701 e13702 e13703 e13704 e13705 e13706 e13707 b13708 b13709 b13710 b13711 b13712 b13713 b13714 b13715 f13309
      omega
    have d13716 : (x 5 9).toNat = 0 := by
      have r13717 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13718 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e13719 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e13720 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e13721 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e13722 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e13723 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b13724 := hb (x (-1) 7)
      have b13725 := hb (x 0 6)
      have b13726 := hb (x 1 5)
      have b13727 := hb (x 2 4)
      have b13728 := hb (x 3 11)
      have b13729 := hb (x 4 10)
      have b13730 := hb (x 5 9)
      have b13731 := hb (x 6 8)
      clear * - r13717 e13718 e13719 e13720 e13721 e13722 e13723 b13724 b13725 b13726 b13727 b13728 b13729 b13730 b13731 d13700 f13309
      omega
    have d13732 : (x 4 10).toNat = 0 := by
      have r13733 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13734 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e13735 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e13736 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e13737 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e13738 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e13739 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b13740 := hb (x (-1) 7)
      have b13741 := hb (x 0 6)
      have b13742 := hb (x 1 5)
      have b13743 := hb (x 2 4)
      have b13744 := hb (x 3 11)
      have b13745 := hb (x 4 10)
      have b13746 := hb (x 5 9)
      have b13747 := hb (x 6 8)
      clear * - r13733 e13734 e13735 e13736 e13737 e13738 e13739 b13740 b13741 b13742 b13743 b13744 b13745 b13746 b13747 d13700 d13716 f13309
      omega
    have d13748 : (x 4 1 && x 4 10).toNat = 0 := by
      have r13749 := hand2 (x 4 1) (x 4 10)
      have b13750 := hb (x 4 10)
      have b13751 := hb (x 4 1 && x 4 10)
      clear * - r13749 b13750 b13751 d13732
      omega
    have d13752 : (x 2 3 && x 2 12).toNat = 1 := by
      have r13753 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13754 := hb (x (-1) 6)
      have b13755 := hb (x 5 9)
      have b13756 := hb (x 4 1 && x 4 10)
      have b13757 := hb (x 3 2 && x 3 11)
      have b13758 := hb (x 2 3 && x 2 12)
      have b13759 := hb (x 1 4 && x 1 13)
      have b13760 := hb (x 0 5 && x 0 14)
      clear * - r13753 b13754 b13755 b13756 b13757 b13758 b13759 b13760 d13716 d13748 d12251 d13347 g39 d13533
      omega
    have d13761 : (x 2 12).toNat = 1 := by
      have r13762 := hand2 (x 2 3) (x 2 12)
      have b13763 := hb (x 2 12)
      have b13764 := hb (x 2 3 && x 2 12)
      clear * - r13762 b13763 b13764 d13752
      omega
    have d13765 : (x 1 13).toNat = 0 := by
      have r13766 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13767 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e13768 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b13769 := hb (x (-1) 3)
      have b13770 := hb (x 0 2)
      have b13771 := hb (x 1 13)
      have b13772 := hb (x 2 12)
      clear * - r13766 e13767 e13768 b13769 b13770 b13771 b13772 d13761 g7
      omega
    have d13773 : (x 1 5).toNat = 0 := by
      have r13774 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
      have b13775 := hb (x 1 5)
      have b13776 := hb (x 1 13)
      clear * - r13774 b13775 b13776 d13765
      omega
    have d13777 : (x (-1) 3).toNat = 0 := by
      have r13778 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13779 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e13780 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b13781 := hb (x (-1) 3)
      have b13782 := hb (x 0 2)
      have b13783 := hb (x 1 13)
      have b13784 := hb (x 2 12)
      clear * - r13778 e13779 e13780 b13781 b13782 b13783 b13784 d13761 d13765 g7
      omega
    have d13785 : (x (-1) 11).toNat = 0 := by
      have r13786 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b13787 := hb (x (-1) 3)
      have b13788 := hb (x (-1) 11)
      clear * - r13786 b13787 b13788 d13777
      omega
    have d13789 : (x 2 3).toNat = 1 := by
      have r13790 := hand1 (x 2 3) (x 2 12)
      have b13791 := hb (x 2 3)
      have b13792 := hb (x 2 3 && x 2 12)
      clear * - r13790 b13791 b13792 d13752
      omega
    have d13793 : (x 5 12).toNat = 0 := by
      have r13794 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13795 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e13796 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b13797 := hb (x 2 3)
      have b13798 := hb (x 3 2)
      have b13799 := hb (x 4 13)
      have b13800 := hb (x 5 12)
      clear * - r13794 e13795 e13796 b13797 b13798 b13799 b13800 d12243 d13789
      omega
    have d13801 : (x 5 1 && x 5 12).toNat = 0 := by
      have r13802 := hand2 (x 5 1) (x 5 12)
      have b13803 := hb (x 5 12)
      have b13804 := hb (x 5 1 && x 5 12)
      clear * - r13802 b13803 b13804 d13793
      omega
    have d13805 : (x 5 4).toNat = 0 := by
      have r13806 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
      have b13807 := hb (x 5 4)
      have b13808 := hb (x 5 12)
      clear * - r13806 b13807 b13808 d13793
      omega
    have d13809 : (x 4 13).toNat = 0 := by
      have r13810 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13811 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e13812 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b13813 := hb (x 2 3)
      have b13814 := hb (x 3 2)
      have b13815 := hb (x 4 13)
      have b13816 := hb (x 5 12)
      clear * - r13810 e13811 e13812 b13813 b13814 b13815 b13816 d13793 d12243 d13789
      omega
    have d13817 : (x 4 2 && x 4 13).toNat = 0 := by
      have r13818 := hand2 (x 4 2) (x 4 13)
      have b13819 := hb (x 4 13)
      have b13820 := hb (x 4 2 && x 4 13)
      clear * - r13818 b13819 b13820 d13809
      omega
    have d13821 : (x 4 5).toNat = 0 := by
      have r13822 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
      have b13823 := hb (x 4 5)
      have b13824 := hb (x 4 13)
      clear * - r13822 b13823 b13824 d13809
      omega
    have d13825 : (x 2 2).toNat = 1 := by
      have r13826 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13827 := hb (x 2 2)
      have b13828 := hb (x 4 13)
      have b13829 := hb (x 3 1 && x 3 14)
      clear * - r13826 b13827 b13828 b13829 d13809 d12231
      omega
    have d13830 : (x 2 14).toNat = 1 := by
      have r13831 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b13832 := hb (x 2 2)
      have b13833 := hb (x 2 14)
      clear * - r13831 b13832 b13833 d13825
      omega
    have d13834 : (x 1 1).toNat = 0 := by
      have r13835 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13836 := hb (x 1 1)
      have b13837 := hb (x 2 14)
      clear * - r13835 b13836 b13837 d13830
      omega
    have d13838 : (x 1 1 && x 1 8).toNat = 0 := by
      have r13839 := hand1 (x 1 1) (x 1 8)
      have b13840 := hb (x 1 1)
      have b13841 := hb (x 1 1 && x 1 8)
      clear * - r13839 b13840 b13841 d13834
      omega
    have d13842 : (x 1 9).toNat = 0 := by
      have r13843 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
      have b13844 := hb (x 1 1)
      have b13845 := hb (x 1 9)
      clear * - r13843 b13844 b13845 d13834
      omega
    have d13846 : (x 3 11).toNat = 0 := by
      have r13847 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13848 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e13849 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e13850 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e13851 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e13852 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e13853 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b13854 := hb (x (-1) 7)
      have b13855 := hb (x 0 6)
      have b13856 := hb (x 1 5)
      have b13857 := hb (x 2 4)
      have b13858 := hb (x 3 11)
      have b13859 := hb (x 4 10)
      have b13860 := hb (x 5 9)
      have b13861 := hb (x 6 8)
      clear * - r13847 e13848 e13849 e13850 e13851 e13852 e13853 b13854 b13855 b13856 b13857 b13858 b13859 b13860 b13861 d13700 d13716 d13732 d13773 f13309
      omega
    have d13862 : (x 2 4).toNat = 0 := by
      have r13863 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13864 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e13865 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e13866 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e13867 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e13868 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e13869 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b13870 := hb (x (-1) 7)
      have b13871 := hb (x 0 6)
      have b13872 := hb (x 1 5)
      have b13873 := hb (x 2 4)
      have b13874 := hb (x 3 11)
      have b13875 := hb (x 4 10)
      have b13876 := hb (x 5 9)
      have b13877 := hb (x 6 8)
      clear * - r13863 e13864 e13865 e13866 e13867 e13868 e13869 b13870 b13871 b13872 b13873 b13874 b13875 b13876 b13877 d13700 d13716 d13732 d13846 d13773 f13309
      omega
    have d13878 : (x 6 11).toNat = 1 := by
      have r13879 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b13880 := hb (x 2 4)
      have b13881 := hb (x 6 11)
      have b13882 := hb (x 5 1 && x 5 12)
      have b13883 := hb (x 4 2 && x 4 13)
      have b13884 := hb (x 3 3 && x 3 14)
      clear * - r13879 b13880 b13881 b13882 b13883 b13884 d13801 d13817 d12235 d13862
      omega
    have d13885 : (x 6 3).toNat = 1 := by
      have r13886 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
      have b13887 := hb (x 6 3)
      have b13888 := hb (x 6 11)
      clear * - r13886 b13887 b13888 d13878
      omega
    have d13889 : (x 9 12).toNat = 0 := by
      have r13890 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13891 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e13892 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b13893 := hb (x 6 3)
      have b13894 := hb (x 7 2)
      have b13895 := hb (x 8 13)
      have b13896 := hb (x 9 12)
      clear * - r13890 e13891 e13892 b13893 b13894 b13895 b13896 d13885
      omega
    have d13897 : (x 8 13).toNat = 0 := by
      have r13898 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13899 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e13900 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b13901 := hb (x 6 3)
      have b13902 := hb (x 7 2)
      have b13903 := hb (x 8 13)
      have b13904 := hb (x 9 12)
      clear * - r13898 e13899 e13900 b13901 b13902 b13903 b13904 d13889 d13885
      omega
    have d13905 : (x 7 2).toNat = 0 := by
      have r13906 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13907 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e13908 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b13909 := hb (x 6 3)
      have b13910 := hb (x 7 2)
      have b13911 := hb (x 8 13)
      have b13912 := hb (x 9 12)
      clear * - r13906 e13907 e13908 b13909 b13910 b13911 b13912 d13889 d13897 d13885
      omega
    have d13913 : (x 7 10).toNat = 0 := by
      have r13914 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
      have b13915 := hb (x 7 2)
      have b13916 := hb (x 7 10)
      clear * - r13914 b13915 b13916 d13905
      omega
    have d13917 : (x 9 8).toNat = 0 := by
      have r13918 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13919 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e13920 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e13921 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e13922 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e13923 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e13924 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b13925 := hb (x 2 7)
      have b13926 := hb (x 3 6)
      have b13927 := hb (x 4 5)
      have b13928 := hb (x 5 4)
      have b13929 := hb (x 6 11)
      have b13930 := hb (x 7 10)
      have b13931 := hb (x 8 9)
      have b13932 := hb (x 9 8)
      clear * - r13918 e13919 e13920 e13921 e13922 e13923 e13924 b13925 b13926 b13927 b13928 b13929 b13930 b13931 b13932 d13913 d13878 d13805 d13821 d12239
      omega
    have d13933 : (x 8 9).toNat = 0 := by
      have r13934 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13935 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e13936 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e13937 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e13938 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e13939 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e13940 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b13941 := hb (x 2 7)
      have b13942 := hb (x 3 6)
      have b13943 := hb (x 4 5)
      have b13944 := hb (x 5 4)
      have b13945 := hb (x 6 11)
      have b13946 := hb (x 7 10)
      have b13947 := hb (x 8 9)
      have b13948 := hb (x 9 8)
      clear * - r13934 e13935 e13936 e13937 e13938 e13939 e13940 b13941 b13942 b13943 b13944 b13945 b13946 b13947 b13948 d13917 d13913 d13878 d13805 d13821 d12239
      omega
    have d13949 : (x 2 7).toNat = 0 := by
      have r13950 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13951 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e13952 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e13953 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e13954 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e13955 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e13956 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have b13957 := hb (x 2 7)
      have b13958 := hb (x 3 6)
      have b13959 := hb (x 4 5)
      have b13960 := hb (x 5 4)
      have b13961 := hb (x 6 11)
      have b13962 := hb (x 7 10)
      have b13963 := hb (x 8 9)
      have b13964 := hb (x 9 8)
      clear * - r13950 e13951 e13952 e13953 e13954 e13955 e13956 b13957 b13958 b13959 b13960 b13961 b13962 b13963 b13964 d13917 d13933 d13913 d13878 d13805 d13821 d12239
      omega
    have d13965 : (x 2 8).toNat = 0 := by
      have r13966 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13967 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e13968 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e13969 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e13970 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e13971 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e13972 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b13973 := hb (x (-5) 7)
      have b13974 := hb (x (-4) 6)
      have b13975 := hb (x (-3) 5)
      have b13976 := hb (x (-2) 4)
      have b13977 := hb (x (-1) 11)
      have b13978 := hb (x 0 10)
      have b13979 := hb (x 1 9)
      have b13980 := hb (x 2 8)
      clear * - r13966 e13967 e13968 e13969 e13970 e13971 e13972 b13973 b13974 b13975 b13976 b13977 b13978 b13979 b13980 d13842 g11 d13785 d13496 d13480
      omega
    have d13981 : (x (-4) 6).toNat = 0 := by
      have r13982 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e13983 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e13984 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e13985 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e13986 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e13987 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e13988 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b13989 := hb (x (-5) 7)
      have b13990 := hb (x (-4) 6)
      have b13991 := hb (x (-3) 5)
      have b13992 := hb (x (-2) 4)
      have b13993 := hb (x (-1) 11)
      have b13994 := hb (x 0 10)
      have b13995 := hb (x 1 9)
      have b13996 := hb (x 2 8)
      clear * - r13982 e13983 e13984 e13985 e13986 e13987 e13988 b13989 b13990 b13991 b13992 b13993 b13994 b13995 b13996 d13965 d13842 g11 d13785 d13496 d13480
      omega
    have d13997 : (x (-4) 6 && x (-4) 13).toNat = 0 := by
      have r13998 := hand1 (x (-4) 6) (x (-4) 13)
      have b13999 := hb (x (-4) 6)
      have b14000 := hb (x (-4) 6 && x (-4) 13)
      clear * - r13998 b13999 b14000 d13981
      omega
    have d14001 : (x (-6) 8).toNat = 0 := by
      have r14002 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e14003 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
      have e14004 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
      have e14005 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
      have e14006 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
      have e14007 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
      have e14008 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
      have b14009 := hb (x (-13) 7)
      have b14010 := hb (x (-12) 6)
      have b14011 := hb (x (-11) 5)
      have b14012 := hb (x (-10) 4)
      have b14013 := hb (x (-9) 11)
      have b14014 := hb (x (-8) 10)
      have b14015 := hb (x (-7) 9)
      have b14016 := hb (x (-6) 8)
      clear * - r14002 e14003 e14004 e14005 e14006 e14007 e14008 b14009 b14010 b14011 b14012 b14013 b14014 b14015 b14016 d13696 d13584 d13600 d13673 d13692
      omega
    have r14017 : 1 ≤ (x 2 7).toNat + (x 1 1 && x 1 8).toNat + (x 0 2 && x 0 9).toNat + (x (-1) 3 && x (-1) 10).toNat + (x (-2) 4 && x (-2) 11).toNat + (x (-3) 5 && x (-3) 12).toNat + (x (-4) 6 && x (-4) 13).toNat + (x (-5) 7 && x (-5) 14).toNat + (x (-6) 8).toNat := by have q := hcov7 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14018 := hb (x (-6) 8)
    have b14019 := hb (x 2 7)
    have b14020 := hb (x 1 1 && x 1 8)
    have b14021 := hb (x 0 2 && x 0 9)
    have b14022 := hb (x (-1) 3 && x (-1) 10)
    have b14023 := hb (x (-2) 4 && x (-2) 11)
    have b14024 := hb (x (-3) 5 && x (-3) 12)
    have b14025 := hb (x (-4) 6 && x (-4) 13)
    have b14026 := hb (x (-5) 7 && x (-5) 14)
    linarith only [r14017, b14018, b14019, b14020, b14021, b14022, b14023, b14024, b14025, b14026, d13949, d13838, d12214, d13363, d13379, d13484, d13997, d13665, d14001]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a00011_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 11).toNat = 0)
    (g1 : (x (-2) 2).toNat = 0)
    (g2 : (x (-2) 10).toNat = 0)
    (g3 : (x (-1) 13).toNat = 0)
    (g4 : (x 0 2).toNat = 1)
    (g5 : (x 0 5).toNat = 0)
    (g6 : (x 0 10).toNat = 0)
    (g7 : (x 0 11).toNat = 0)
    (g8 : (x 1 2).toNat = 0)
    (g9 : (x 1 6).toNat = 0)
    (g10 : (x 1 10).toNat = 0)
    (g11 : (x 3 9).toNat = 0)
    (g12 : (x 4 8).toNat = 0)
    (g13 : (x 0 4 && x 0 10).toNat = 0)
    (g14 : (x (-1) 5 && x (-1) 11).toNat = 0)
    (g15 : (x (-2) 6 && x (-2) 12).toNat = 0)
    (g16 : (x (-3) 7 && x (-3) 13).toNat = 0)
    (g17 : (x 1 6 && x 1 12).toNat = 0)
    (g18 : (x 4 8 && x 4 14).toNat = 0)
    (g19 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g20 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g21 : (x 1 3 && x 1 10).toNat = 0)
    (g22 : (x 0 4 && x 0 11).toNat = 0)
    (g23 : (x (-1) 5 && x (-1) 12).toNat = 0)
    (g24 : (x (-2) 6 && x (-2) 13).toNat = 0)
    (g25 : (x (-3) 7 && x (-3) 14).toNat = 0)
    (g26 : (x 2 1 && x 2 10).toNat = 0)
    (g27 : (x 1 2 && x 1 11).toNat = 0)
    (g28 : (x 0 3 && x 0 12).toNat = 0)
    (g29 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g30 : (x 0 5 && x 0 14).toNat = 0)
    (g31 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g32 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g33 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g34 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g35 : (x 1 2 && x 1 13).toNat = 0)
    (g36 : (x 0 3 && x 0 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d14028 : (x 0 14).toNat = 1 := by
    have r14029 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
    have b14030 := hb (x 0 2)
    have b14031 := hb (x 0 14)
    clear * - r14029 b14030 b14031 g4
    omega
  have d14032 : (x (-1) 1).toNat = 0 := by
    have r14033 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14034 := hb (x (-1) 1)
    have b14035 := hb (x 0 14)
    clear * - r14033 b14034 b14035 d14028
    omega
  have d14036 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
    have r14037 := hand1 (x (-1) 1) (x (-1) 14)
    have b14038 := hb (x (-1) 1)
    have b14039 := hb (x (-1) 1 && x (-1) 14)
    clear * - r14037 b14038 b14039 d14032
    omega
  have d14040 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
    have r14041 := hand1 (x (-1) 1) (x (-1) 12)
    have b14042 := hb (x (-1) 1)
    have b14043 := hb (x (-1) 1 && x (-1) 12)
    clear * - r14041 b14042 b14043 d14032
    omega
  have d14044 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
    have r14045 := hand1 (x (-1) 1) (x (-1) 11)
    have b14046 := hb (x (-1) 1)
    have b14047 := hb (x (-1) 1 && x (-1) 11)
    clear * - r14045 b14046 b14047 d14032
    omega
  have d14048 : (x (-1) 1 && x (-1) 8).toNat = 0 := by
    have r14049 := hand1 (x (-1) 1) (x (-1) 8)
    have b14050 := hb (x (-1) 1)
    have b14051 := hb (x (-1) 1 && x (-1) 8)
    clear * - r14049 b14050 b14051 d14032
    omega
  have d14052 : (x (-1) 9).toNat = 0 := by
    have r14053 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
    have b14054 := hb (x (-1) 1)
    have b14055 := hb (x (-1) 9)
    clear * - r14053 b14054 b14055 d14032
    omega
  have d14056 : (x 0 13).toNat = 1 := by
    have r14057 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14058 := hb (x (-2) 2)
    have b14059 := hb (x 0 13)
    have b14060 := hb (x (-1) 1 && x (-1) 14)
    clear * - r14057 b14058 b14059 b14060 d14036 g1
    omega
  have d14061 : (x 2 12).toNat = 0 := by
    have r14062 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14063 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e14064 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b14065 := hb (x (-1) 3)
    have b14066 := hb (x 0 2)
    have b14067 := hb (x 1 13)
    have b14068 := hb (x 2 12)
    clear * - r14062 e14063 e14064 b14065 b14066 b14067 b14068 g4
    omega
  have d14069 : (x 2 1 && x 2 12).toNat = 0 := by
    have r14070 := hand2 (x 2 1) (x 2 12)
    have b14071 := hb (x 2 12)
    have b14072 := hb (x 2 1 && x 2 12)
    clear * - r14070 b14071 b14072 d14061
    omega
  have d14073 : (x 2 3 && x 2 12).toNat = 0 := by
    have r14074 := hand2 (x 2 3) (x 2 12)
    have b14075 := hb (x 2 12)
    have b14076 := hb (x 2 3 && x 2 12)
    clear * - r14074 b14075 b14076 d14061
    omega
  have d14077 : (x 2 6 && x 2 12).toNat = 0 := by
    have r14078 := hand2 (x 2 6) (x 2 12)
    have b14079 := hb (x 2 12)
    have b14080 := hb (x 2 6 && x 2 12)
    clear * - r14078 b14079 b14080 d14061
    omega
  have d14081 : (x 2 4).toNat = 0 := by
    have r14082 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b14083 := hb (x 2 4)
    have b14084 := hb (x 2 12)
    clear * - r14082 b14083 b14084 d14061
    omega
  have d14085 : (x 1 13).toNat = 0 := by
    have r14086 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14087 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e14088 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b14089 := hb (x (-1) 3)
    have b14090 := hb (x 0 2)
    have b14091 := hb (x 1 13)
    have b14092 := hb (x 2 12)
    clear * - r14086 e14087 e14088 b14089 b14090 b14091 b14092 d14061 g4
    omega
  have d14093 : (x 1 4 && x 1 13).toNat = 0 := by
    have r14094 := hand2 (x 1 4) (x 1 13)
    have b14095 := hb (x 1 13)
    have b14096 := hb (x 1 4 && x 1 13)
    clear * - r14094 b14095 b14096 d14085
    omega
  have d14097 : (x 1 7 && x 1 13).toNat = 0 := by
    have r14098 := hand2 (x 1 7) (x 1 13)
    have b14099 := hb (x 1 13)
    have b14100 := hb (x 1 7 && x 1 13)
    clear * - r14098 b14099 b14100 d14085
    omega
  have d14101 : (x 1 5).toNat = 0 := by
    have r14102 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b14103 := hb (x 1 5)
    have b14104 := hb (x 1 13)
    clear * - r14102 b14103 b14104 d14085
    omega
  have d14105 : (x 1 12).toNat = 0 := by
    have r14106 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14107 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e14108 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b14109 := hb (x (-2) 3)
    have b14110 := hb (x (-1) 2)
    have b14111 := hb (x 0 13)
    have b14112 := hb (x 1 12)
    clear * - r14106 e14107 e14108 b14109 b14110 b14111 b14112 d14056
    omega
  have d14113 : (x 1 4).toNat = 0 := by
    have r14114 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
    have b14115 := hb (x 1 4)
    have b14116 := hb (x 1 12)
    clear * - r14114 b14115 b14116 d14105
    omega
  have d14117 : (x (-1) 2).toNat = 0 := by
    have r14118 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14119 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e14120 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b14121 := hb (x (-2) 3)
    have b14122 := hb (x (-1) 2)
    have b14123 := hb (x 0 13)
    have b14124 := hb (x 1 12)
    clear * - r14118 e14119 e14120 b14121 b14122 b14123 b14124 d14105 d14056
    omega
  have d14125 : (x (-1) 10).toNat = 0 := by
    have r14126 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
    have b14127 := hb (x (-1) 2)
    have b14128 := hb (x (-1) 10)
    clear * - r14126 b14127 b14128 d14117
    omega
  have d14129 : (x (-2) 3).toNat = 0 := by
    have r14130 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14131 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e14132 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b14133 := hb (x (-2) 3)
    have b14134 := hb (x (-1) 2)
    have b14135 := hb (x 0 13)
    have b14136 := hb (x 1 12)
    clear * - r14130 e14131 e14132 b14133 b14134 b14135 b14136 d14105 d14056 d14117
    omega
  have d14137 : (x (-2) 11).toNat = 0 := by
    have r14138 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
    have b14139 := hb (x (-2) 3)
    have b14140 := hb (x (-2) 11)
    clear * - r14138 b14139 b14140 d14129
    omega
  have d14141 : (x (-2) 1 && x (-2) 11).toNat = 0 := by
    have r14142 := hand2 (x (-2) 1) (x (-2) 11)
    have b14143 := hb (x (-2) 11)
    have b14144 := hb (x (-2) 1 && x (-2) 11)
    clear * - r14142 b14143 b14144 d14137
    omega
  have d14145 : (x (-4) 4).toNat = 1 := by
    have r14146 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14147 := hb (x (-4) 4)
    have b14148 := hb (x 0 11)
    have b14149 := hb (x (-1) 1 && x (-1) 12)
    have b14150 := hb (x (-2) 2 && x (-2) 13)
    have b14151 := hb (x (-3) 3 && x (-3) 14)
    clear * - r14146 b14147 b14148 b14149 b14150 b14151 g7 d14040 g33 g34
    omega
  have d14152 : (x (-4) 12).toNat = 1 := by
    have r14153 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have b14154 := hb (x (-4) 4)
    have b14155 := hb (x (-4) 12)
    clear * - r14153 b14154 b14155 d14145
    omega
  have d14156 : (x (-5) 13).toNat = 0 := by
    have r14157 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14158 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e14159 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b14160 := hb (x (-7) 3)
    have b14161 := hb (x (-6) 2)
    have b14162 := hb (x (-5) 13)
    have b14163 := hb (x (-4) 12)
    clear * - r14157 e14158 e14159 b14160 b14161 b14162 b14163 d14152
    omega
  have d14164 : (x (-5) 5).toNat = 0 := by
    have r14165 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b14166 := hb (x (-5) 5)
    have b14167 := hb (x (-5) 13)
    clear * - r14165 b14166 b14167 d14156
    omega
  have d14168 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
    have r14169 := hand1 (x (-5) 5) (x (-5) 12)
    have b14170 := hb (x (-5) 5)
    have b14171 := hb (x (-5) 5 && x (-5) 12)
    clear * - r14169 b14170 b14171 d14164
    omega
  have d14172 : (x (-6) 2).toNat = 0 := by
    have r14173 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14174 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e14175 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b14176 := hb (x (-7) 3)
    have b14177 := hb (x (-6) 2)
    have b14178 := hb (x (-5) 13)
    have b14179 := hb (x (-4) 12)
    clear * - r14173 e14174 e14175 b14176 b14177 b14178 b14179 d14152 d14156
    omega
  have d14180 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
    have r14181 := hand1 (x (-6) 2) (x (-6) 13)
    have b14182 := hb (x (-6) 2)
    have b14183 := hb (x (-6) 2 && x (-6) 13)
    clear * - r14181 b14182 b14183 d14172
    omega
  have d14184 : (x (-6) 10).toNat = 0 := by
    have r14185 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
    have b14186 := hb (x (-6) 2)
    have b14187 := hb (x (-6) 10)
    clear * - r14185 b14186 b14187 d14172
    omega
  have d14188 : (x (-7) 3).toNat = 0 := by
    have r14189 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14190 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e14191 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b14192 := hb (x (-7) 3)
    have b14193 := hb (x (-6) 2)
    have b14194 := hb (x (-5) 13)
    have b14195 := hb (x (-4) 12)
    clear * - r14189 e14190 e14191 b14192 b14193 b14194 b14195 d14152 d14156 d14172
    omega
  have d14196 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
    have r14197 := hand1 (x (-7) 3) (x (-7) 14)
    have b14198 := hb (x (-7) 3)
    have b14199 := hb (x (-7) 3 && x (-7) 14)
    clear * - r14197 b14198 b14199 d14188
    omega
  have d14200 : (x (-7) 11).toNat = 0 := by
    have r14201 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have b14202 := hb (x (-7) 3)
    have b14203 := hb (x (-7) 11)
    clear * - r14201 b14202 b14203 d14188
    omega
  have d14204 : (x (-4) 4 && x (-4) 14).toNat = 1 := by
    have r14205 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14206 := hb (x (-5) 5)
    have b14207 := hb (x 0 10)
    have b14208 := hb (x (-1) 1 && x (-1) 11)
    have b14209 := hb (x (-2) 2 && x (-2) 12)
    have b14210 := hb (x (-3) 3 && x (-3) 13)
    have b14211 := hb (x (-4) 4 && x (-4) 14)
    clear * - r14205 b14206 b14207 b14208 b14209 b14210 b14211 g6 d14044 g31 g32 d14164
    omega
  have d14212 : (x (-4) 14).toNat = 1 := by
    have r14213 := hand2 (x (-4) 4) (x (-4) 14)
    have b14214 := hb (x (-4) 14)
    have b14215 := hb (x (-4) 4 && x (-4) 14)
    clear * - r14213 b14214 b14215 d14204
    omega
  have d14216 : (x (-5) 1).toNat = 0 := by
    have r14217 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14218 := hb (x (-5) 1)
    have b14219 := hb (x (-4) 14)
    clear * - r14217 b14218 b14219 d14212
    omega
  have d14220 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
    have r14221 := hand1 (x (-5) 1) (x (-5) 14)
    have b14222 := hb (x (-5) 1)
    have b14223 := hb (x (-5) 1 && x (-5) 14)
    clear * - r14221 b14222 b14223 d14216
    omega
  have d14224 : (x (-4) 13).toNat = 1 := by
    have r14225 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14226 := hb (x (-6) 2)
    have b14227 := hb (x (-4) 13)
    have b14228 := hb (x (-5) 1 && x (-5) 14)
    clear * - r14225 b14226 b14227 b14228 d14220 d14172
    omega
  have d14229 : (x (-4) 1).toNat = 1 := by
    have r14230 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b14231 := hb (x (-4) 1)
    have b14232 := hb (x (-4) 13)
    clear * - r14230 b14231 b14232 d14224
    omega
  have d14233 : (x (-3) 14).toNat = 0 := by
    have r14234 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14235 := hb (x (-4) 1)
    have b14236 := hb (x (-3) 14)
    clear * - r14234 b14235 b14236 d14229
    omega
  have d14237 : (x (-3) 6).toNat = 0 := by
    have r14238 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
    have b14239 := hb (x (-3) 6)
    have b14240 := hb (x (-3) 14)
    clear * - r14238 b14239 b14240 d14233
    omega
  have d14241 : (x (-3) 2).toNat = 0 := by
    have r14242 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b14243 := hb (x (-3) 2)
    have b14244 := hb (x (-3) 14)
    clear * - r14242 b14243 b14244 d14233
    omega
  have d14245 : (x (-3) 2 && x (-3) 12).toNat = 0 := by
    have r14246 := hand1 (x (-3) 2) (x (-3) 12)
    have b14247 := hb (x (-3) 2)
    have b14248 := hb (x (-3) 2 && x (-3) 12)
    clear * - r14246 b14247 b14248 d14241
    omega
  have d14249 : (x (-3) 10).toNat = 0 := by
    have r14250 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
    have b14251 := hb (x (-3) 2)
    have b14252 := hb (x (-3) 10)
    clear * - r14250 b14251 b14252 d14241
    omega
  have d14253 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
    have r14254 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14255 := hb (x (-3) 2)
    have b14256 := hb (x (-1) 13)
    have b14257 := hb (x (-2) 1 && x (-2) 14)
    clear * - r14254 b14255 b14256 b14257 g3 d14241
    omega
  have d14258 : (x (-2) 1).toNat = 1 := by
    have r14259 := hand1 (x (-2) 1) (x (-2) 14)
    have b14260 := hb (x (-2) 1)
    have b14261 := hb (x (-2) 1 && x (-2) 14)
    clear * - r14259 b14260 b14261 d14253
    omega
  have d14262 : (x (-1) 14).toNat = 0 := by
    have r14263 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14264 := hb (x (-2) 1)
    have b14265 := hb (x (-1) 14)
    clear * - r14263 b14264 b14265 d14258
    omega
  have d14266 : (x (-1) 8 && x (-1) 14).toNat = 0 := by
    have r14267 := hand2 (x (-1) 8) (x (-1) 14)
    have b14268 := hb (x (-1) 14)
    have b14269 := hb (x (-1) 8 && x (-1) 14)
    clear * - r14267 b14268 b14269 d14262
    omega
  have d14270 : (x (-1) 6).toNat = 0 := by
    have r14271 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
    have b14272 := hb (x (-1) 6)
    have b14273 := hb (x (-1) 14)
    clear * - r14271 b14272 b14273 d14262
    omega
  have d14274 : (x (-3) 12).toNat = 0 := by
    have r14275 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14276 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e14277 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b14278 := hb (x (-6) 3)
    have b14279 := hb (x (-5) 2)
    have b14280 := hb (x (-4) 13)
    have b14281 := hb (x (-3) 12)
    clear * - r14275 e14276 e14277 b14278 b14279 b14280 b14281 d14224
    omega
  have d14282 : (x (-5) 2).toNat = 0 := by
    have r14283 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14284 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e14285 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b14286 := hb (x (-6) 3)
    have b14287 := hb (x (-5) 2)
    have b14288 := hb (x (-4) 13)
    have b14289 := hb (x (-3) 12)
    clear * - r14283 e14284 e14285 b14286 b14287 b14288 b14289 d14274 d14224
    omega
  have d14290 : (x (-5) 10).toNat = 0 := by
    have r14291 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
    have b14292 := hb (x (-5) 2)
    have b14293 := hb (x (-5) 10)
    clear * - r14291 b14292 b14293 d14282
    omega
  have d14294 : (x (-6) 3).toNat = 0 := by
    have r14295 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14296 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e14297 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b14298 := hb (x (-6) 3)
    have b14299 := hb (x (-5) 2)
    have b14300 := hb (x (-4) 13)
    have b14301 := hb (x (-3) 12)
    clear * - r14295 e14296 e14297 b14298 b14299 b14300 b14301 d14274 d14224 d14282
    omega
  have d14302 : (x (-6) 11).toNat = 0 := by
    have r14303 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
    have b14304 := hb (x (-6) 3)
    have b14305 := hb (x (-6) 11)
    clear * - r14303 b14304 b14305 d14294
    omega
  have d14306 : (x (-6) 1 && x (-6) 11).toNat = 0 := by
    have r14307 := hand2 (x (-6) 1) (x (-6) 11)
    have b14308 := hb (x (-6) 11)
    have b14309 := hb (x (-6) 1 && x (-6) 11)
    clear * - r14307 b14308 b14309 d14302
    omega
  have d14310 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
    have r14311 := hand1 (x (-5) 1) (x (-5) 12)
    have b14312 := hb (x (-5) 1)
    have b14313 := hb (x (-5) 1 && x (-5) 12)
    clear * - r14311 b14312 b14313 d14216
    omega
  have d14314 : (x (-5) 9).toNat = 0 := by
    have r14315 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
    have b14316 := hb (x (-5) 1)
    have b14317 := hb (x (-5) 9)
    clear * - r14315 b14316 b14317 d14216
    omega
  have d14318 : (x (-2) 5 && x (-2) 14).toNat = 1 := by
    have r14319 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14320 := hb (x (-3) 6)
    have b14321 := hb (x 3 9)
    have b14322 := hb (x 2 1 && x 2 10)
    have b14323 := hb (x 1 2 && x 1 11)
    have b14324 := hb (x 0 3 && x 0 12)
    have b14325 := hb (x (-1) 4 && x (-1) 13)
    have b14326 := hb (x (-2) 5 && x (-2) 14)
    clear * - r14319 b14320 b14321 b14322 b14323 b14324 b14325 b14326 g11 g26 g27 g28 g29 d14237
    omega
  have d14327 : (x (-2) 5).toNat = 1 := by
    have r14328 := hand1 (x (-2) 5) (x (-2) 14)
    have b14329 := hb (x (-2) 5)
    have b14330 := hb (x (-2) 5 && x (-2) 14)
    clear * - r14328 b14329 b14330 d14318
    omega
  have d14331 : (x (-2) 13).toNat = 1 := by
    have r14332 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
    have b14333 := hb (x (-2) 5)
    have b14334 := hb (x (-2) 13)
    clear * - r14332 b14333 b14334 d14327
    omega
  have d14335 : (x (-1) 12).toNat = 0 := by
    have r14336 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14337 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e14338 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b14339 := hb (x (-4) 3)
    have b14340 := hb (x (-3) 2)
    have b14341 := hb (x (-2) 13)
    have b14342 := hb (x (-1) 12)
    clear * - r14336 e14337 e14338 b14339 b14340 b14341 b14342 d14331 d14241
    omega
  have d14343 : (x (-1) 4).toNat = 0 := by
    have r14344 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b14345 := hb (x (-1) 4)
    have b14346 := hb (x (-1) 12)
    clear * - r14344 b14345 b14346 d14335
    omega
  have d14347 : (x 3 11).toNat = 1 := by
    have r14348 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14349 := hb (x (-1) 4)
    have b14350 := hb (x 3 11)
    have b14351 := hb (x 2 1 && x 2 12)
    have b14352 := hb (x 1 2 && x 1 13)
    have b14353 := hb (x 0 3 && x 0 14)
    clear * - r14348 b14349 b14350 b14351 b14352 b14353 d14069 g35 g36 d14343
    omega
  have d14354 : (x 3 3).toNat = 1 := by
    have r14355 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b14356 := hb (x 3 3)
    have b14357 := hb (x 3 11)
    clear * - r14355 b14356 b14357 d14347
    omega
  have d14358 : (x 6 12).toNat = 0 := by
    have r14359 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14360 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e14361 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b14362 := hb (x 3 3)
    have b14363 := hb (x 4 2)
    have b14364 := hb (x 5 13)
    have b14365 := hb (x 6 12)
    clear * - r14359 e14360 e14361 b14362 b14363 b14364 b14365 d14354
    omega
  have d14366 : (x 6 3 && x 6 12).toNat = 0 := by
    have r14367 := hand2 (x 6 3) (x 6 12)
    have b14368 := hb (x 6 12)
    have b14369 := hb (x 6 3 && x 6 12)
    clear * - r14367 b14368 b14369 d14358
    omega
  have d14370 : (x 6 5 && x 6 12).toNat = 0 := by
    have r14371 := hand2 (x 6 5) (x 6 12)
    have b14372 := hb (x 6 12)
    have b14373 := hb (x 6 5 && x 6 12)
    clear * - r14371 b14372 b14373 d14358
    omega
  have d14374 : (x 6 6 && x 6 12).toNat = 0 := by
    have r14375 := hand2 (x 6 6) (x 6 12)
    have b14376 := hb (x 6 12)
    have b14377 := hb (x 6 6 && x 6 12)
    clear * - r14375 b14376 b14377 d14358
    omega
  have d14378 : (x 6 4).toNat = 0 := by
    have r14379 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
    have b14380 := hb (x 6 4)
    have b14381 := hb (x 6 12)
    clear * - r14379 b14380 b14381 d14358
    omega
  have d14382 : (x 6 4 && x 6 13).toNat = 0 := by
    have r14383 := hand1 (x 6 4) (x 6 13)
    have b14384 := hb (x 6 4)
    have b14385 := hb (x 6 4 && x 6 13)
    clear * - r14383 b14384 b14385 d14378
    omega
  have d14386 : (x 5 13).toNat = 0 := by
    have r14387 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14388 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e14389 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b14390 := hb (x 3 3)
    have b14391 := hb (x 4 2)
    have b14392 := hb (x 5 13)
    have b14393 := hb (x 6 12)
    clear * - r14387 e14388 e14389 b14390 b14391 b14392 b14393 d14358 d14354
    omega
  have d14394 : (x 5 4 && x 5 13).toNat = 0 := by
    have r14395 := hand2 (x 5 4) (x 5 13)
    have b14396 := hb (x 5 13)
    have b14397 := hb (x 5 4 && x 5 13)
    clear * - r14395 b14396 b14397 d14386
    omega
  have d14398 : (x 5 6 && x 5 13).toNat = 0 := by
    have r14399 := hand2 (x 5 6) (x 5 13)
    have b14400 := hb (x 5 13)
    have b14401 := hb (x 5 6 && x 5 13)
    clear * - r14399 b14400 b14401 d14386
    omega
  have d14402 : (x 5 7 && x 5 13).toNat = 0 := by
    have r14403 := hand2 (x 5 7) (x 5 13)
    have b14404 := hb (x 5 13)
    have b14405 := hb (x 5 7 && x 5 13)
    clear * - r14403 b14404 b14405 d14386
    omega
  have d14406 : (x 5 5).toNat = 0 := by
    have r14407 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
    have b14408 := hb (x 5 5)
    have b14409 := hb (x 5 13)
    clear * - r14407 b14408 b14409 d14386
    omega
  have d14410 : (x 5 5 && x 5 14).toNat = 0 := by
    have r14411 := hand1 (x 5 5) (x 5 14)
    have b14412 := hb (x 5 5)
    have b14413 := hb (x 5 5 && x 5 14)
    clear * - r14411 b14412 b14413 d14406
    omega
  have d14414 : (x 4 2).toNat = 0 := by
    have r14415 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14416 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e14417 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b14418 := hb (x 3 3)
    have b14419 := hb (x 4 2)
    have b14420 := hb (x 5 13)
    have b14421 := hb (x 6 12)
    clear * - r14415 e14416 e14417 b14418 b14419 b14420 b14421 d14358 d14386 d14354
    omega
  have d14422 : (x 4 10).toNat = 0 := by
    have r14423 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
    have b14424 := hb (x 4 2)
    have b14425 := hb (x 4 10)
    clear * - r14423 b14424 b14425 d14414
    omega
  have d14426 : (x 4 1 && x 4 10).toNat = 0 := by
    have r14427 := hand2 (x 4 1) (x 4 10)
    have b14428 := hb (x 4 10)
    have b14429 := hb (x 4 1 && x 4 10)
    clear * - r14427 b14428 b14429 d14422
    omega
  have d14430 : (x 4 4 && x 4 10).toNat = 0 := by
    have r14431 := hand2 (x 4 4) (x 4 10)
    have b14432 := hb (x 4 10)
    have b14433 := hb (x 4 4 && x 4 10)
    clear * - r14431 b14432 b14433 d14422
    omega
  have d14434 : (x (-4) 3).toNat = 0 := by
    have r14435 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14436 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e14437 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b14438 := hb (x (-4) 3)
    have b14439 := hb (x (-3) 2)
    have b14440 := hb (x (-2) 13)
    have b14441 := hb (x (-1) 12)
    clear * - r14435 e14436 e14437 b14438 b14439 b14440 b14441 d14335 d14331 d14241
    omega
  have d14442 : (x (-4) 3 && x (-4) 13).toNat = 0 := by
    have r14443 := hand1 (x (-4) 3) (x (-4) 13)
    have b14444 := hb (x (-4) 3)
    have b14445 := hb (x (-4) 3 && x (-4) 13)
    clear * - r14443 b14444 b14445 d14434
    omega
  have d14446 : (x (-4) 11).toNat = 0 := by
    have r14447 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
    have b14448 := hb (x (-4) 3)
    have b14449 := hb (x (-4) 11)
    clear * - r14447 b14448 b14449 d14434
    omega
  have d14450 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
    have r14451 := hand2 (x (-4) 4) (x (-4) 11)
    have b14452 := hb (x (-4) 11)
    have b14453 := hb (x (-4) 4 && x (-4) 11)
    clear * - r14451 b14452 b14453 d14446
    omega
  have d14454 : (x (-8) 4).toNat = 1 := by
    have r14455 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14456 := hb (x (-8) 4)
    have b14457 := hb (x (-4) 11)
    have b14458 := hb (x (-5) 1 && x (-5) 12)
    have b14459 := hb (x (-6) 2 && x (-6) 13)
    have b14460 := hb (x (-7) 3 && x (-7) 14)
    clear * - r14455 b14456 b14457 b14458 b14459 b14460 d14446 d14310 d14180 d14196
    omega
  have d14461 : (x (-8) 12).toNat = 1 := by
    have r14462 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
    have b14463 := hb (x (-8) 4)
    have b14464 := hb (x (-8) 12)
    clear * - r14462 b14463 b14464 d14454
    omega
  have d14465 : (x (-9) 13).toNat = 0 := by
    have r14466 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14467 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
    have e14468 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
    have b14469 := hb (x (-11) 3)
    have b14470 := hb (x (-10) 2)
    have b14471 := hb (x (-9) 13)
    have b14472 := hb (x (-8) 12)
    clear * - r14466 e14467 e14468 b14469 b14470 b14471 b14472 d14461
    omega
  have d14473 : (x (-9) 5).toNat = 0 := by
    have r14474 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
    have b14475 := hb (x (-9) 5)
    have b14476 := hb (x (-9) 13)
    clear * - r14474 b14475 b14476 d14465
    omega
  have d14477 : (x (-10) 2).toNat = 0 := by
    have r14478 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14479 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
    have e14480 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
    have b14481 := hb (x (-11) 3)
    have b14482 := hb (x (-10) 2)
    have b14483 := hb (x (-9) 13)
    have b14484 := hb (x (-8) 12)
    clear * - r14478 e14479 e14480 b14481 b14482 b14483 b14484 d14461 d14465
    omega
  have d14485 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
    have r14486 := hand1 (x (-10) 2) (x (-10) 13)
    have b14487 := hb (x (-10) 2)
    have b14488 := hb (x (-10) 2 && x (-10) 13)
    clear * - r14486 b14487 b14488 d14477
    omega
  have d14489 : (x (-10) 10).toNat = 0 := by
    have r14490 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
    have b14491 := hb (x (-10) 2)
    have b14492 := hb (x (-10) 10)
    clear * - r14490 b14491 b14492 d14477
    omega
  have d14493 : (x (-11) 3).toNat = 0 := by
    have r14494 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14495 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
    have e14496 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
    have b14497 := hb (x (-11) 3)
    have b14498 := hb (x (-10) 2)
    have b14499 := hb (x (-9) 13)
    have b14500 := hb (x (-8) 12)
    clear * - r14494 e14495 e14496 b14497 b14498 b14499 b14500 d14461 d14465 d14477
    omega
  have d14501 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
    have r14502 := hand1 (x (-11) 3) (x (-11) 14)
    have b14503 := hb (x (-11) 3)
    have b14504 := hb (x (-11) 3 && x (-11) 14)
    clear * - r14502 b14503 b14504 d14493
    omega
  have d14505 : (x (-11) 11).toNat = 0 := by
    have r14506 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
    have b14507 := hb (x (-11) 3)
    have b14508 := hb (x (-11) 11)
    clear * - r14506 b14507 b14508 d14493
    omega
  have d14509 : (x 6 8).toNat = 0 := by
    have r14510 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14511 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e14512 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e14513 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e14514 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e14515 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e14516 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b14517 := hb (x (-1) 7)
    have b14518 := hb (x 0 6)
    have b14519 := hb (x 1 5)
    have b14520 := hb (x 2 4)
    have b14521 := hb (x 3 11)
    have b14522 := hb (x 4 10)
    have b14523 := hb (x 5 9)
    have b14524 := hb (x 6 8)
    clear * - r14510 e14511 e14512 e14513 e14514 e14515 e14516 b14517 b14518 b14519 b14520 b14521 b14522 b14523 b14524 d14422 d14347 d14081 d14101
    omega
  have d14525 : (x 6 2 && x 6 8).toNat = 0 := by
    have r14526 := hand2 (x 6 2) (x 6 8)
    have b14527 := hb (x 6 8)
    have b14528 := hb (x 6 2 && x 6 8)
    clear * - r14526 b14527 b14528 d14509
    omega
  have d14529 : (x 5 9).toNat = 0 := by
    have r14530 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14531 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e14532 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e14533 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e14534 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e14535 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e14536 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b14537 := hb (x (-1) 7)
    have b14538 := hb (x 0 6)
    have b14539 := hb (x 1 5)
    have b14540 := hb (x 2 4)
    have b14541 := hb (x 3 11)
    have b14542 := hb (x 4 10)
    have b14543 := hb (x 5 9)
    have b14544 := hb (x 6 8)
    clear * - r14530 e14531 e14532 e14533 e14534 e14535 e14536 b14537 b14538 b14539 b14540 b14541 b14542 b14543 b14544 d14509 d14422 d14347 d14081 d14101
    omega
  have d14545 : (x 5 3 && x 5 9).toNat = 0 := by
    have r14546 := hand2 (x 5 3) (x 5 9)
    have b14547 := hb (x 5 9)
    have b14548 := hb (x 5 3 && x 5 9)
    clear * - r14546 b14547 b14548 d14529
    omega
  have d14549 : (x 3 2 && x 3 11).toNat = 1 := by
    have r14550 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14551 := hb (x (-1) 6)
    have b14552 := hb (x 5 9)
    have b14553 := hb (x 4 1 && x 4 10)
    have b14554 := hb (x 3 2 && x 3 11)
    have b14555 := hb (x 2 3 && x 2 12)
    have b14556 := hb (x 1 4 && x 1 13)
    have b14557 := hb (x 0 5 && x 0 14)
    clear * - r14550 b14551 b14552 b14553 b14554 b14555 b14556 b14557 d14529 d14426 d14073 d14093 g30 d14270
    omega
  have d14558 : (x 3 2).toNat = 1 := by
    have r14559 := hand1 (x 3 2) (x 3 11)
    have b14560 := hb (x 3 2)
    have b14561 := hb (x 3 2 && x 3 11)
    clear * - r14559 b14560 b14561 d14549
    omega
  have d14562 : (x 3 14).toNat = 1 := by
    have r14563 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b14564 := hb (x 3 2)
    have b14565 := hb (x 3 14)
    clear * - r14563 b14564 b14565 d14558
    omega
  have d14566 : (x 2 1).toNat = 0 := by
    have r14567 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14568 := hb (x 2 1)
    have b14569 := hb (x 3 14)
    clear * - r14567 b14568 b14569 d14562
    omega
  have d14570 : (x 2 1 && x 2 14).toNat = 0 := by
    have r14571 := hand1 (x 2 1) (x 2 14)
    have b14572 := hb (x 2 1)
    have b14573 := hb (x 2 1 && x 2 14)
    clear * - r14571 b14572 b14573 d14566
    omega
  have d14574 : (x 3 13).toNat = 1 := by
    have r14575 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14576 := hb (x 1 2)
    have b14577 := hb (x 3 13)
    have b14578 := hb (x 2 1 && x 2 14)
    clear * - r14575 b14576 b14577 b14578 d14570 g8
    omega
  have d14579 : (x 3 1).toNat = 1 := by
    have r14580 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b14581 := hb (x 3 1)
    have b14582 := hb (x 3 13)
    clear * - r14580 b14581 b14582 d14574
    omega
  have d14583 : (x 4 14).toNat = 0 := by
    have r14584 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14585 := hb (x 3 1)
    have b14586 := hb (x 4 14)
    clear * - r14584 b14585 b14586 d14579
    omega
  have d14587 : (x 4 5 && x 4 14).toNat = 0 := by
    have r14588 := hand2 (x 4 5) (x 4 14)
    have b14589 := hb (x 4 14)
    have b14590 := hb (x 4 5 && x 4 14)
    clear * - r14588 b14589 b14590 d14583
    omega
  have d14591 : (x 4 7 && x 4 14).toNat = 0 := by
    have r14592 := hand2 (x 4 7) (x 4 14)
    have b14593 := hb (x 4 14)
    have b14594 := hb (x 4 7 && x 4 14)
    clear * - r14592 b14593 b14594 d14583
    omega
  have d14595 : (x 4 6).toNat = 0 := by
    have r14596 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
    have b14597 := hb (x 4 6)
    have b14598 := hb (x 4 14)
    clear * - r14596 b14597 b14598 d14583
    omega
  have d14599 : (x 4 12).toNat = 0 := by
    have r14600 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14601 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e14602 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b14603 := hb (x 1 3)
    have b14604 := hb (x 2 2)
    have b14605 := hb (x 3 13)
    have b14606 := hb (x 4 12)
    clear * - r14600 e14601 e14602 b14603 b14604 b14605 b14606 d14574
    omega
  have d14607 : (x 4 3 && x 4 12).toNat = 0 := by
    have r14608 := hand2 (x 4 3) (x 4 12)
    have b14609 := hb (x 4 12)
    have b14610 := hb (x 4 3 && x 4 12)
    clear * - r14608 b14609 b14610 d14599
    omega
  have d14611 : (x 4 4).toNat = 0 := by
    have r14612 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b14613 := hb (x 4 4)
    have b14614 := hb (x 4 12)
    clear * - r14612 b14613 b14614 d14599
    omega
  have d14615 : (x 2 2).toNat = 0 := by
    have r14616 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14617 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e14618 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b14619 := hb (x 1 3)
    have b14620 := hb (x 2 2)
    have b14621 := hb (x 3 13)
    have b14622 := hb (x 4 12)
    clear * - r14616 e14617 e14618 b14619 b14620 b14621 b14622 d14599 d14574
    omega
  have d14623 : (x 2 2 && x 2 9).toNat = 0 := by
    have r14624 := hand1 (x 2 2) (x 2 9)
    have b14625 := hb (x 2 2)
    have b14626 := hb (x 2 2 && x 2 9)
    clear * - r14624 b14625 b14626 d14615
    omega
  have d14627 : (x 2 2 && x 2 8).toNat = 0 := by
    have r14628 := hand1 (x 2 2) (x 2 8)
    have b14629 := hb (x 2 2)
    have b14630 := hb (x 2 2 && x 2 8)
    clear * - r14628 b14629 b14630 d14615
    omega
  have d14631 : (x 1 3).toNat = 0 := by
    have r14632 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14633 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e14634 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b14635 := hb (x 1 3)
    have b14636 := hb (x 2 2)
    have b14637 := hb (x 3 13)
    have b14638 := hb (x 4 12)
    clear * - r14632 e14633 e14634 b14635 b14636 b14637 b14638 d14599 d14574 d14615
    omega
  have d14639 : (x 1 3 && x 1 9).toNat = 0 := by
    have r14640 := hand1 (x 1 3) (x 1 9)
    have b14641 := hb (x 1 3)
    have b14642 := hb (x 1 3 && x 1 9)
    clear * - r14640 b14641 b14642 d14631
    omega
  have d14643 : (x 2 13).toNat = 0 := by
    have r14644 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
    have b14645 := hb (x 2 1)
    have b14646 := hb (x 2 13)
    clear * - r14644 b14645 b14646 d14566
    omega
  have d14647 : (x 2 5).toNat = 0 := by
    have r14648 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
    have b14649 := hb (x 2 5)
    have b14650 := hb (x 2 13)
    clear * - r14648 b14649 b14650 d14643
    omega
  have d14651 : (x 2 5 && x 2 14).toNat = 0 := by
    have r14652 := hand1 (x 2 5) (x 2 14)
    have b14653 := hb (x 2 5)
    have b14654 := hb (x 2 5 && x 2 14)
    clear * - r14652 b14653 b14654 d14647
    omega
  have d14655 : (x 2 5 && x 2 11).toNat = 0 := by
    have r14656 := hand1 (x 2 5) (x 2 11)
    have b14657 := hb (x 2 5)
    have b14658 := hb (x 2 5 && x 2 11)
    clear * - r14656 b14657 b14658 d14647
    omega
  have d14659 : (x 2 9).toNat = 0 := by
    have r14660 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
    have b14661 := hb (x 2 1)
    have b14662 := hb (x 2 9)
    clear * - r14660 b14661 b14662 d14566
    omega
  have d14663 : (x 5 12).toNat = 0 := by
    have r14664 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14665 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e14666 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b14667 := hb (x 2 3)
    have b14668 := hb (x 3 2)
    have b14669 := hb (x 4 13)
    have b14670 := hb (x 5 12)
    clear * - r14664 e14665 e14666 b14667 b14668 b14669 b14670 d14558
    omega
  have d14671 : (x 5 6 && x 5 12).toNat = 0 := by
    have r14672 := hand2 (x 5 6) (x 5 12)
    have b14673 := hb (x 5 12)
    have b14674 := hb (x 5 6 && x 5 12)
    clear * - r14672 b14673 b14674 d14663
    omega
  have d14675 : (x 5 4).toNat = 0 := by
    have r14676 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b14677 := hb (x 5 4)
    have b14678 := hb (x 5 12)
    clear * - r14676 b14677 b14678 d14663
    omega
  have d14679 : (x 5 4 && x 5 14).toNat = 0 := by
    have r14680 := hand1 (x 5 4) (x 5 14)
    have b14681 := hb (x 5 4)
    have b14682 := hb (x 5 4 && x 5 14)
    clear * - r14680 b14681 b14682 d14675
    omega
  have d14683 : (x 4 13).toNat = 0 := by
    have r14684 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14685 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e14686 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b14687 := hb (x 2 3)
    have b14688 := hb (x 3 2)
    have b14689 := hb (x 4 13)
    have b14690 := hb (x 5 12)
    clear * - r14684 e14685 e14686 b14687 b14688 b14689 b14690 d14663 d14558
    omega
  have d14691 : (x 4 7 && x 4 13).toNat = 0 := by
    have r14692 := hand2 (x 4 7) (x 4 13)
    have b14693 := hb (x 4 13)
    have b14694 := hb (x 4 7 && x 4 13)
    clear * - r14692 b14693 b14694 d14683
    omega
  have d14695 : (x 4 5).toNat = 0 := by
    have r14696 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
    have b14697 := hb (x 4 5)
    have b14698 := hb (x 4 13)
    clear * - r14696 b14697 b14698 d14683
    omega
  have d14699 : (x 2 3).toNat = 0 := by
    have r14700 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14701 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e14702 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b14703 := hb (x 2 3)
    have b14704 := hb (x 3 2)
    have b14705 := hb (x 4 13)
    have b14706 := hb (x 5 12)
    clear * - r14700 e14701 e14702 b14703 b14704 b14705 b14706 d14663 d14683 d14558
    omega
  have d14707 : (x 2 11).toNat = 0 := by
    have r14708 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
    have b14709 := hb (x 2 3)
    have b14710 := hb (x 2 11)
    clear * - r14708 b14709 b14710 d14699
    omega
  have d14711 : (x 3 8).toNat = 0 := by
    have r14712 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14713 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e14714 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e14715 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e14716 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e14717 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e14718 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b14719 := hb (x (-4) 7)
    have b14720 := hb (x (-3) 6)
    have b14721 := hb (x (-2) 5)
    have b14722 := hb (x (-1) 4)
    have b14723 := hb (x 0 11)
    have b14724 := hb (x 1 10)
    have b14725 := hb (x 2 9)
    have b14726 := hb (x 3 8)
    clear * - r14712 e14713 e14714 e14715 e14716 e14717 e14718 b14719 b14720 b14721 b14722 b14723 b14724 b14725 b14726 d14659 g10 g7 d14343 d14327 d14237
    omega
  have d14727 : (x 3 1 && x 3 8).toNat = 0 := by
    have r14728 := hand2 (x 3 1) (x 3 8)
    have b14729 := hb (x 3 8)
    have b14730 := hb (x 3 1 && x 3 8)
    clear * - r14728 b14729 b14730 d14711
    omega
  have d14731 : (x 3 8 && x 3 14).toNat = 0 := by
    have r14732 := hand1 (x 3 8) (x 3 14)
    have b14733 := hb (x 3 8)
    have b14734 := hb (x 3 8 && x 3 14)
    clear * - r14732 b14733 b14734 d14711
    omega
  have d14735 : (x 0 8).toNat = 0 := by
    have r14736 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14737 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e14738 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e14739 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e14740 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e14741 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e14742 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b14743 := hb (x (-7) 7)
    have b14744 := hb (x (-6) 6)
    have b14745 := hb (x (-5) 5)
    have b14746 := hb (x (-4) 4)
    have b14747 := hb (x (-3) 11)
    have b14748 := hb (x (-2) 10)
    have b14749 := hb (x (-1) 9)
    have b14750 := hb (x 0 8)
    clear * - r14736 e14737 e14738 e14739 e14740 e14741 e14742 b14743 b14744 b14745 b14746 b14747 b14748 b14749 b14750 d14052 g2 g0 d14145 d14164
    omega
  have d14751 : (x 0 8 && x 0 14).toNat = 0 := by
    have r14752 := hand1 (x 0 8) (x 0 14)
    have b14753 := hb (x 0 8)
    have b14754 := hb (x 0 8 && x 0 14)
    clear * - r14752 b14753 b14754 d14735
    omega
  have d14755 : (x (-6) 6).toNat = 0 := by
    have r14756 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14757 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e14758 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e14759 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e14760 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e14761 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e14762 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b14763 := hb (x (-7) 7)
    have b14764 := hb (x (-6) 6)
    have b14765 := hb (x (-5) 5)
    have b14766 := hb (x (-4) 4)
    have b14767 := hb (x (-3) 11)
    have b14768 := hb (x (-2) 10)
    have b14769 := hb (x (-1) 9)
    have b14770 := hb (x 0 8)
    clear * - r14756 e14757 e14758 e14759 e14760 e14761 e14762 b14763 b14764 b14765 b14766 b14767 b14768 b14769 b14770 d14735 d14052 g2 g0 d14145 d14164
    omega
  have d14771 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
    have r14772 := hand1 (x (-6) 6) (x (-6) 13)
    have b14773 := hb (x (-6) 6)
    have b14774 := hb (x (-6) 6 && x (-6) 13)
    clear * - r14772 b14773 b14774 d14755
    omega
  have d14775 : (x (-7) 7).toNat = 0 := by
    have r14776 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14777 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e14778 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e14779 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e14780 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e14781 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e14782 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b14783 := hb (x (-7) 7)
    have b14784 := hb (x (-6) 6)
    have b14785 := hb (x (-5) 5)
    have b14786 := hb (x (-4) 4)
    have b14787 := hb (x (-3) 11)
    have b14788 := hb (x (-2) 10)
    have b14789 := hb (x (-1) 9)
    have b14790 := hb (x 0 8)
    clear * - r14776 e14777 e14778 e14779 e14780 e14781 e14782 b14783 b14784 b14785 b14786 b14787 b14788 b14789 b14790 d14735 d14052 g2 g0 d14145 d14164 d14755
    omega
  have d14791 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
    have r14792 := hand1 (x (-7) 7) (x (-7) 14)
    have b14793 := hb (x (-7) 7)
    have b14794 := hb (x (-7) 7 && x (-7) 14)
    clear * - r14792 b14793 b14794 d14775
    omega
  have d14795 : (x (-4) 8).toNat = 0 := by
    have r14796 : (x (-4) 8).toNat + (x (-5) 1 && x (-5) 9).toNat + (x (-6) 2 && x (-6) 10).toNat + (x (-7) 3 && x (-7) 11).toNat + (x (-8) 4 && x (-8) 12).toNat + (x (-9) 5 && x (-9) 13).toNat + (x (-10) 6 && x (-10) 14).toNat + (x (-11) 7).toNat = 1 := by have q := hd8 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14797 : (x (-5) 1 && x (-5) 9).toNat = (x (-5) 9).toNat := handr _ _ (fun h => hp9 (-5) (h))
    have e14798 : (x (-6) 2 && x (-6) 10).toNat = (x (-6) 10).toNat := handr _ _ (fun h => hp10 (-6) (h))
    have e14799 : (x (-7) 3 && x (-7) 11).toNat = (x (-7) 11).toNat := handr _ _ (fun h => hp11 (-7) (h))
    have e14800 : (x (-8) 4 && x (-8) 12).toNat = (x (-8) 4).toNat := handl _ _ (fun h => hp4 (-8) (h))
    have e14801 : (x (-9) 5 && x (-9) 13).toNat = (x (-9) 5).toNat := handl _ _ (fun h => hp5 (-9) (h))
    have e14802 : (x (-10) 6 && x (-10) 14).toNat = (x (-10) 6).toNat := handl _ _ (fun h => hp6 (-10) (h))
    have b14803 := hb (x (-11) 7)
    have b14804 := hb (x (-10) 6)
    have b14805 := hb (x (-9) 5)
    have b14806 := hb (x (-8) 4)
    have b14807 := hb (x (-7) 11)
    have b14808 := hb (x (-6) 10)
    have b14809 := hb (x (-5) 9)
    have b14810 := hb (x (-4) 8)
    clear * - r14796 e14797 e14798 e14799 e14800 e14801 e14802 b14803 b14804 b14805 b14806 b14807 b14808 b14809 b14810 d14314 d14184 d14200 d14454 d14473
    omega
  have d14811 : (x (-4) 8 && x (-4) 14).toNat = 0 := by
    have r14812 := hand1 (x (-4) 8) (x (-4) 14)
    have b14813 := hb (x (-4) 8)
    have b14814 := hb (x (-4) 8 && x (-4) 14)
    clear * - r14812 b14813 b14814 d14795
    omega
  have d14815 : (x 4 7).toNat = 1 := by
    have r14816 : 1 ≤ (x 4 7).toNat + (x 3 1 && x 3 8).toNat + (x 2 2 && x 2 9).toNat + (x 1 3 && x 1 10).toNat + (x 0 4 && x 0 11).toNat + (x (-1) 5 && x (-1) 12).toNat + (x (-2) 6 && x (-2) 13).toNat + (x (-3) 7 && x (-3) 14).toNat + (x (-4) 8).toNat := by have q := hcov7 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14817 := hb (x (-4) 8)
    have b14818 := hb (x 4 7)
    have b14819 := hb (x 3 1 && x 3 8)
    have b14820 := hb (x 2 2 && x 2 9)
    have b14821 := hb (x 1 3 && x 1 10)
    have b14822 := hb (x 0 4 && x 0 11)
    have b14823 := hb (x (-1) 5 && x (-1) 12)
    have b14824 := hb (x (-2) 6 && x (-2) 13)
    have b14825 := hb (x (-3) 7 && x (-3) 14)
    clear * - r14816 b14817 b14818 b14819 b14820 b14821 b14822 b14823 b14824 b14825 d14727 d14623 g21 g22 g23 g24 g25 d14795
    omega
  have d14826 : (x 11 8).toNat = 0 := by
    have r14827 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14828 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e14829 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e14830 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e14831 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e14832 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e14833 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b14834 := hb (x 4 7)
    have b14835 := hb (x 5 6)
    have b14836 := hb (x 6 5)
    have b14837 := hb (x 7 4)
    have b14838 := hb (x 8 11)
    have b14839 := hb (x 9 10)
    have b14840 := hb (x 10 9)
    have b14841 := hb (x 11 8)
    clear * - r14827 e14828 e14829 e14830 e14831 e14832 e14833 b14834 b14835 b14836 b14837 b14838 b14839 b14840 b14841 d14815
    omega
  have d14842 : (x 11 1 && x 11 8).toNat = 0 := by
    have r14843 := hand2 (x 11 1) (x 11 8)
    have b14844 := hb (x 11 8)
    have b14845 := hb (x 11 1 && x 11 8)
    clear * - r14843 b14844 b14845 d14826
    omega
  have d14846 : (x 11 2 && x 11 8).toNat = 0 := by
    have r14847 := hand2 (x 11 2) (x 11 8)
    have b14848 := hb (x 11 8)
    have b14849 := hb (x 11 2 && x 11 8)
    clear * - r14847 b14848 b14849 d14826
    omega
  have d14850 : (x 10 9).toNat = 0 := by
    have r14851 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14852 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e14853 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e14854 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e14855 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e14856 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e14857 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b14858 := hb (x 4 7)
    have b14859 := hb (x 5 6)
    have b14860 := hb (x 6 5)
    have b14861 := hb (x 7 4)
    have b14862 := hb (x 8 11)
    have b14863 := hb (x 9 10)
    have b14864 := hb (x 10 9)
    have b14865 := hb (x 11 8)
    clear * - r14851 e14852 e14853 e14854 e14855 e14856 e14857 b14858 b14859 b14860 b14861 b14862 b14863 b14864 b14865 d14826 d14815
    omega
  have d14866 : (x 10 2 && x 10 9).toNat = 0 := by
    have r14867 := hand2 (x 10 2) (x 10 9)
    have b14868 := hb (x 10 9)
    have b14869 := hb (x 10 2 && x 10 9)
    clear * - r14867 b14868 b14869 d14850
    omega
  have d14870 : (x 10 3 && x 10 9).toNat = 0 := by
    have r14871 := hand2 (x 10 3) (x 10 9)
    have b14872 := hb (x 10 9)
    have b14873 := hb (x 10 3 && x 10 9)
    clear * - r14871 b14872 b14873 d14850
    omega
  have d14874 : (x 9 10).toNat = 0 := by
    have r14875 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14876 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e14877 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e14878 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e14879 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e14880 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e14881 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b14882 := hb (x 4 7)
    have b14883 := hb (x 5 6)
    have b14884 := hb (x 6 5)
    have b14885 := hb (x 7 4)
    have b14886 := hb (x 8 11)
    have b14887 := hb (x 9 10)
    have b14888 := hb (x 10 9)
    have b14889 := hb (x 11 8)
    clear * - r14875 e14876 e14877 e14878 e14879 e14880 e14881 b14882 b14883 b14884 b14885 b14886 b14887 b14888 b14889 d14826 d14850 d14815
    omega
  have d14890 : (x 9 1 && x 9 10).toNat = 0 := by
    have r14891 := hand2 (x 9 1) (x 9 10)
    have b14892 := hb (x 9 10)
    have b14893 := hb (x 9 1 && x 9 10)
    clear * - r14891 b14892 b14893 d14874
    omega
  have d14894 : (x 9 3 && x 9 10).toNat = 0 := by
    have r14895 := hand2 (x 9 3) (x 9 10)
    have b14896 := hb (x 9 10)
    have b14897 := hb (x 9 3 && x 9 10)
    clear * - r14895 b14896 b14897 d14874
    omega
  have d14898 : (x 9 4 && x 9 10).toNat = 0 := by
    have r14899 := hand2 (x 9 4) (x 9 10)
    have b14900 := hb (x 9 10)
    have b14901 := hb (x 9 4 && x 9 10)
    clear * - r14899 b14900 b14901 d14874
    omega
  have d14902 : (x 8 11).toNat = 0 := by
    have r14903 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14904 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e14905 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e14906 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e14907 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e14908 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e14909 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b14910 := hb (x 4 7)
    have b14911 := hb (x 5 6)
    have b14912 := hb (x 6 5)
    have b14913 := hb (x 7 4)
    have b14914 := hb (x 8 11)
    have b14915 := hb (x 9 10)
    have b14916 := hb (x 10 9)
    have b14917 := hb (x 11 8)
    clear * - r14903 e14904 e14905 e14906 e14907 e14908 e14909 b14910 b14911 b14912 b14913 b14914 b14915 b14916 b14917 d14826 d14850 d14874 d14815
    omega
  have d14918 : (x 8 1 && x 8 11).toNat = 0 := by
    have r14919 := hand2 (x 8 1) (x 8 11)
    have b14920 := hb (x 8 11)
    have b14921 := hb (x 8 1 && x 8 11)
    clear * - r14919 b14920 b14921 d14902
    omega
  have d14922 : (x 8 2 && x 8 11).toNat = 0 := by
    have r14923 := hand2 (x 8 2) (x 8 11)
    have b14924 := hb (x 8 11)
    have b14925 := hb (x 8 2 && x 8 11)
    clear * - r14923 b14924 b14925 d14902
    omega
  have d14926 : (x 7 3 && x 7 12).toNat = 1 := by
    have r14927 : 1 ≤ (x 10 9).toNat + (x 9 1 && x 9 10).toNat + (x 8 2 && x 8 11).toNat + (x 7 3 && x 7 12).toNat + (x 6 4 && x 6 13).toNat + (x 5 5 && x 5 14).toNat + (x 4 6).toNat := by have q := hcov9 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14928 := hb (x 4 6)
    have b14929 := hb (x 10 9)
    have b14930 := hb (x 9 1 && x 9 10)
    have b14931 := hb (x 8 2 && x 8 11)
    have b14932 := hb (x 7 3 && x 7 12)
    have b14933 := hb (x 6 4 && x 6 13)
    have b14934 := hb (x 5 5 && x 5 14)
    clear * - r14927 b14928 b14929 b14930 b14931 b14932 b14933 b14934 d14850 d14890 d14922 d14382 d14410 d14595
    omega
  have d14935 : (x 7 12).toNat = 1 := by
    have r14936 := hand2 (x 7 3) (x 7 12)
    have b14937 := hb (x 7 12)
    have b14938 := hb (x 7 3 && x 7 12)
    clear * - r14936 b14937 b14938 d14926
    omega
  have d14939 : (x 6 13).toNat = 0 := by
    have r14940 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14941 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e14942 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b14943 := hb (x 4 3)
    have b14944 := hb (x 5 2)
    have b14945 := hb (x 6 13)
    have b14946 := hb (x 7 12)
    clear * - r14940 e14941 e14942 b14943 b14944 b14945 b14946 d14935
    omega
  have d14947 : (x 6 3 && x 6 13).toNat = 0 := by
    have r14948 := hand2 (x 6 3) (x 6 13)
    have b14949 := hb (x 6 13)
    have b14950 := hb (x 6 3 && x 6 13)
    clear * - r14948 b14949 b14950 d14939
    omega
  have d14951 : (x 7 2 && x 7 12).toNat = 1 := by
    have r14952 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14953 := hb (x 4 5)
    have b14954 := hb (x 9 10)
    have b14955 := hb (x 8 1 && x 8 11)
    have b14956 := hb (x 7 2 && x 7 12)
    have b14957 := hb (x 6 3 && x 6 13)
    have b14958 := hb (x 5 4 && x 5 14)
    clear * - r14952 b14953 b14954 b14955 b14956 b14957 b14958 d14874 d14918 d14947 d14679 d14695
    omega
  have d14959 : (x 7 2).toNat = 1 := by
    have r14960 := hand1 (x 7 2) (x 7 12)
    have b14961 := hb (x 7 2)
    have b14962 := hb (x 7 2 && x 7 12)
    clear * - r14960 b14961 b14962 d14951
    omega
  have d14963 : (x 7 14).toNat = 1 := by
    have r14964 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b14965 := hb (x 7 2)
    have b14966 := hb (x 7 14)
    clear * - r14964 b14965 b14966 d14959
    omega
  have d14967 : (x 6 1).toNat = 0 := by
    have r14968 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b14969 := hb (x 6 1)
    have b14970 := hb (x 7 14)
    clear * - r14968 b14969 b14970 d14963
    omega
  have d14971 : (x 6 1 && x 6 14).toNat = 0 := by
    have r14972 := hand1 (x 6 1) (x 6 14)
    have b14973 := hb (x 6 1)
    have b14974 := hb (x 6 1 && x 6 14)
    clear * - r14972 b14973 b14974 d14967
    omega
  have d14975 : (x 6 1 && x 6 10).toNat = 0 := by
    have r14976 := hand1 (x 6 1) (x 6 10)
    have b14977 := hb (x 6 1)
    have b14978 := hb (x 6 1 && x 6 10)
    clear * - r14976 b14977 b14978 d14967
    omega
  have d14979 : (x 6 1 && x 6 7).toNat = 0 := by
    have r14980 := hand1 (x 6 1) (x 6 7)
    have b14981 := hb (x 6 1)
    have b14982 := hb (x 6 1 && x 6 7)
    clear * - r14980 b14981 b14982 d14967
    omega
  have d14983 : (x 6 9).toNat = 0 := by
    have r14984 : (x 6 9).toNat ≤ (x 6 1).toNat := himp _ _ (hp9 6)
    have b14985 := hb (x 6 1)
    have b14986 := hb (x 6 9)
    clear * - r14984 b14985 b14986 d14967
    omega
  have d14987 : (x 9 12).toNat = 0 := by
    have r14988 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e14989 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e14990 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b14991 := hb (x 6 3)
    have b14992 := hb (x 7 2)
    have b14993 := hb (x 8 13)
    have b14994 := hb (x 9 12)
    clear * - r14988 e14989 e14990 b14991 b14992 b14993 b14994 d14959
    omega
  have d14995 : (x 9 2 && x 9 12).toNat = 0 := by
    have r14996 := hand2 (x 9 2) (x 9 12)
    have b14997 := hb (x 9 12)
    have b14998 := hb (x 9 2 && x 9 12)
    clear * - r14996 b14997 b14998 d14987
    omega
  have d14999 : (x 9 4).toNat = 0 := by
    have r15000 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
    have b15001 := hb (x 9 4)
    have b15002 := hb (x 9 12)
    clear * - r15000 b15001 b15002 d14987
    omega
  have d15003 : (x 8 13).toNat = 0 := by
    have r15004 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15005 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e15006 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b15007 := hb (x 6 3)
    have b15008 := hb (x 7 2)
    have b15009 := hb (x 8 13)
    have b15010 := hb (x 9 12)
    clear * - r15004 e15005 e15006 b15007 b15008 b15009 b15010 d14987 d14959
    omega
  have d15011 : (x 8 3 && x 8 13).toNat = 0 := by
    have r15012 := hand2 (x 8 3) (x 8 13)
    have b15013 := hb (x 8 13)
    have b15014 := hb (x 8 3 && x 8 13)
    clear * - r15012 b15013 b15014 d15003
    omega
  have d15015 : (x 8 5).toNat = 0 := by
    have r15016 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
    have b15017 := hb (x 8 5)
    have b15018 := hb (x 8 13)
    clear * - r15016 b15017 b15018 d15003
    omega
  have d15019 : (x 8 5 && x 8 11).toNat = 0 := by
    have r15020 := hand1 (x 8 5) (x 8 11)
    have b15021 := hb (x 8 5)
    have b15022 := hb (x 8 5 && x 8 11)
    clear * - r15020 b15021 b15022 d15015
    omega
  have d15023 : (x 6 3).toNat = 0 := by
    have r15024 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15025 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e15026 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b15027 := hb (x 6 3)
    have b15028 := hb (x 7 2)
    have b15029 := hb (x 8 13)
    have b15030 := hb (x 9 12)
    clear * - r15024 e15025 e15026 b15027 b15028 b15029 b15030 d14987 d15003 d14959
    omega
  have d15031 : (x 6 11).toNat = 0 := by
    have r15032 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
    have b15033 := hb (x 6 3)
    have b15034 := hb (x 6 11)
    clear * - r15032 b15033 b15034 d15023
    omega
  have d15035 : (x 6 5 && x 6 11).toNat = 0 := by
    have r15036 := hand2 (x 6 5) (x 6 11)
    have b15037 := hb (x 6 11)
    have b15038 := hb (x 6 5 && x 6 11)
    clear * - r15036 b15037 b15038 d15031
    omega
  have d15039 : (x 6 6 && x 6 13).toNat = 0 := by
    have r15040 := hand2 (x 6 6) (x 6 13)
    have b15041 := hb (x 6 13)
    have b15042 := hb (x 6 6 && x 6 13)
    clear * - r15040 b15041 b15042 d14939
    omega
  have d15043 : (x 6 7 && x 6 13).toNat = 0 := by
    have r15044 := hand2 (x 6 7) (x 6 13)
    have b15045 := hb (x 6 13)
    have b15046 := hb (x 6 7 && x 6 13)
    clear * - r15044 b15045 b15046 d14939
    omega
  have d15047 : (x 6 5).toNat = 0 := by
    have r15048 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
    have b15049 := hb (x 6 5)
    have b15050 := hb (x 6 13)
    clear * - r15048 b15049 b15050 d14939
    omega
  have d15051 : (x 6 5 && x 6 14).toNat = 0 := by
    have r15052 := hand1 (x 6 5) (x 6 14)
    have b15053 := hb (x 6 5)
    have b15054 := hb (x 6 5 && x 6 14)
    clear * - r15052 b15053 b15054 d15047
    omega
  have d15055 : (x 5 1 && x 5 14).toNat = 1 := by
    have r15056 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15057 := hb (x 4 2)
    have b15058 := hb (x 6 13)
    have b15059 := hb (x 5 1 && x 5 14)
    clear * - r15056 b15057 b15058 b15059 d14939 d14414
    omega
  have d15060 : (x 5 14).toNat = 1 := by
    have r15061 := hand2 (x 5 1) (x 5 14)
    have b15062 := hb (x 5 14)
    have b15063 := hb (x 5 1 && x 5 14)
    clear * - r15061 b15062 b15063 d15055
    omega
  have d15064 : (x 4 1).toNat = 0 := by
    have r15065 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15066 := hb (x 4 1)
    have b15067 := hb (x 5 14)
    clear * - r15065 b15066 b15067 d15060
    omega
  have d15068 : (x 4 9).toNat = 0 := by
    have r15069 : (x 4 9).toNat ≤ (x 4 1).toNat := himp _ _ (hp9 4)
    have b15070 := hb (x 4 1)
    have b15071 := hb (x 4 9)
    clear * - r15069 b15070 b15071 d15064
    omega
  have d15072 : (x 4 3 && x 4 9).toNat = 0 := by
    have r15073 := hand2 (x 4 3) (x 4 9)
    have b15074 := hb (x 4 9)
    have b15075 := hb (x 4 3 && x 4 9)
    clear * - r15073 b15074 b15075 d15068
    omega
  have d15076 : (x 5 1).toNat = 1 := by
    have r15077 := hand1 (x 5 1) (x 5 14)
    have b15078 := hb (x 5 1)
    have b15079 := hb (x 5 1 && x 5 14)
    clear * - r15077 b15078 b15079 d15055
    omega
  have d15080 : (x 6 14).toNat = 0 := by
    have r15081 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15082 := hb (x 5 1)
    have b15083 := hb (x 6 14)
    clear * - r15081 b15082 b15083 d15076
    omega
  have d15084 : (x 6 6).toNat = 0 := by
    have r15085 : (x 6 6).toNat ≤ (x 6 14).toNat := himp _ _ (hp6 6)
    have b15086 := hb (x 6 6)
    have b15087 := hb (x 6 14)
    clear * - r15085 b15086 b15087 d15080
    omega
  have d15088 : (x 6 2).toNat = 0 := by
    have r15089 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
    have b15090 := hb (x 6 2)
    have b15091 := hb (x 6 14)
    clear * - r15089 b15090 b15091 d15080
    omega
  have d15092 : (x 6 10).toNat = 0 := by
    have r15093 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
    have b15094 := hb (x 6 2)
    have b15095 := hb (x 6 10)
    clear * - r15093 b15094 b15095 d15088
    omega
  have d15096 : (x 7 1 && x 7 14).toNat = 1 := by
    have r15097 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15098 := hb (x 6 2)
    have b15099 := hb (x 8 13)
    have b15100 := hb (x 7 1 && x 7 14)
    clear * - r15097 b15098 b15099 b15100 d15003 d15088
    omega
  have d15101 : (x 7 1).toNat = 1 := by
    have r15102 := hand1 (x 7 1) (x 7 14)
    have b15103 := hb (x 7 1)
    have b15104 := hb (x 7 1 && x 7 14)
    clear * - r15102 b15103 b15104 d15096
    omega
  have d15105 : (x 8 14).toNat = 0 := by
    have r15106 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15107 := hb (x 7 1)
    have b15108 := hb (x 8 14)
    clear * - r15106 b15107 b15108 d15101
    omega
  have d15109 : (x 8 3 && x 8 14).toNat = 0 := by
    have r15110 := hand2 (x 8 3) (x 8 14)
    have b15111 := hb (x 8 14)
    have b15112 := hb (x 8 3 && x 8 14)
    clear * - r15110 b15111 b15112 d15105
    omega
  have d15113 : (x 8 6).toNat = 0 := by
    have r15114 : (x 8 6).toNat ≤ (x 8 14).toNat := himp _ _ (hp6 8)
    have b15115 := hb (x 8 6)
    have b15116 := hb (x 8 14)
    clear * - r15114 b15115 b15116 d15105
    omega
  have d15117 : (x 8 2).toNat = 0 := by
    have r15118 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
    have b15119 := hb (x 8 2)
    have b15120 := hb (x 8 14)
    clear * - r15118 b15119 b15120 d15105
    omega
  have d15121 : (x 8 10).toNat = 0 := by
    have r15122 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
    have b15123 := hb (x 8 2)
    have b15124 := hb (x 8 10)
    clear * - r15122 b15123 b15124 d15117
    omega
  have d15125 : (x 8 1 && x 8 10).toNat = 0 := by
    have r15126 := hand2 (x 8 1) (x 8 10)
    have b15127 := hb (x 8 10)
    have b15128 := hb (x 8 1 && x 8 10)
    clear * - r15126 b15127 b15128 d15121
    omega
  have d15129 : (x 8 3 && x 8 10).toNat = 0 := by
    have r15130 := hand2 (x 8 3) (x 8 10)
    have b15131 := hb (x 8 10)
    have b15132 := hb (x 8 3 && x 8 10)
    clear * - r15130 b15131 b15132 d15121
    omega
  have d15133 : (x 8 4 && x 8 10).toNat = 0 := by
    have r15134 := hand2 (x 8 4) (x 8 10)
    have b15135 := hb (x 8 10)
    have b15136 := hb (x 8 4 && x 8 10)
    clear * - r15134 b15135 b15136 d15121
    omega
  have d15137 : (x 5 2).toNat = 0 := by
    have r15138 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15139 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e15140 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b15141 := hb (x 4 3)
    have b15142 := hb (x 5 2)
    have b15143 := hb (x 6 13)
    have b15144 := hb (x 7 12)
    clear * - r15138 e15139 e15140 b15141 b15142 b15143 b15144 d14935 d14939
    omega
  have d15145 : (x 5 2 && x 5 11).toNat = 0 := by
    have r15146 := hand1 (x 5 2) (x 5 11)
    have b15147 := hb (x 5 2)
    have b15148 := hb (x 5 2 && x 5 11)
    clear * - r15146 b15147 b15148 d15137
    omega
  have d15149 : (x 5 2 && x 5 8).toNat = 0 := by
    have r15150 := hand1 (x 5 2) (x 5 8)
    have b15151 := hb (x 5 2)
    have b15152 := hb (x 5 2 && x 5 8)
    clear * - r15150 b15151 b15152 d15137
    omega
  have d15153 : (x 5 10).toNat = 0 := by
    have r15154 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
    have b15155 := hb (x 5 2)
    have b15156 := hb (x 5 10)
    clear * - r15154 b15155 b15156 d15137
    omega
  have d15157 : (x 7 13).toNat = 1 := by
    have r15158 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15159 := hb (x 5 2)
    have b15160 := hb (x 7 13)
    have b15161 := hb (x 6 1 && x 6 14)
    clear * - r15158 b15159 b15160 b15161 d14971 d15137
    omega
  have d15162 : (x 8 12).toNat = 0 := by
    have r15163 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15164 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e15165 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b15166 := hb (x 5 3)
    have b15167 := hb (x 6 2)
    have b15168 := hb (x 7 13)
    have b15169 := hb (x 8 12)
    clear * - r15163 e15164 e15165 b15166 b15167 b15168 b15169 d15157 d15088
    omega
  have d15170 : (x 8 3 && x 8 12).toNat = 0 := by
    have r15171 := hand2 (x 8 3) (x 8 12)
    have b15172 := hb (x 8 12)
    have b15173 := hb (x 8 3 && x 8 12)
    clear * - r15171 b15172 b15173 d15162
    omega
  have d15174 : (x 8 4).toNat = 0 := by
    have r15175 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
    have b15176 := hb (x 8 4)
    have b15177 := hb (x 8 12)
    clear * - r15175 b15176 b15177 d15162
    omega
  have d15178 : (x 8 4 && x 8 11).toNat = 0 := by
    have r15179 := hand1 (x 8 4) (x 8 11)
    have b15180 := hb (x 8 4)
    have b15181 := hb (x 8 4 && x 8 11)
    clear * - r15179 b15180 b15181 d15174
    omega
  have d15182 : (x 5 3).toNat = 0 := by
    have r15183 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15184 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e15185 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b15186 := hb (x 5 3)
    have b15187 := hb (x 6 2)
    have b15188 := hb (x 7 13)
    have b15189 := hb (x 8 12)
    clear * - r15183 e15184 e15185 b15186 b15187 b15188 b15189 d15162 d15157 d15088
    omega
  have d15190 : (x 5 11).toNat = 0 := by
    have r15191 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
    have b15192 := hb (x 5 3)
    have b15193 := hb (x 5 11)
    clear * - r15191 b15192 b15193 d15182
    omega
  have d15194 : (x 4 3).toNat = 0 := by
    have r15195 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15196 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e15197 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b15198 := hb (x 4 3)
    have b15199 := hb (x 5 2)
    have b15200 := hb (x 6 13)
    have b15201 := hb (x 7 12)
    clear * - r15195 e15196 e15197 b15198 b15199 b15200 b15201 d14935 d14939 d15137
    omega
  have d15202 : (x 4 11).toNat = 0 := by
    have r15203 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have b15204 := hb (x 4 3)
    have b15205 := hb (x 4 11)
    clear * - r15203 b15204 b15205 d15194
    omega
  have d15206 : (x 7 3).toNat = 1 := by
    have r15207 := hand1 (x 7 3) (x 7 12)
    have b15208 := hb (x 7 3)
    have b15209 := hb (x 7 3 && x 7 12)
    clear * - r15207 b15208 b15209 d14926
    omega
  have d15210 : (x 10 12).toNat = 0 := by
    have r15211 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15212 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e15213 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b15214 := hb (x 7 3)
    have b15215 := hb (x 8 2)
    have b15216 := hb (x 9 13)
    have b15217 := hb (x 10 12)
    clear * - r15211 e15212 e15213 b15214 b15215 b15216 b15217 d15117 d15206
    omega
  have d15218 : (x 10 1 && x 10 12).toNat = 0 := by
    have r15219 := hand2 (x 10 1) (x 10 12)
    have b15220 := hb (x 10 12)
    have b15221 := hb (x 10 1 && x 10 12)
    clear * - r15219 b15220 b15221 d15210
    omega
  have d15222 : (x 10 4).toNat = 0 := by
    have r15223 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
    have b15224 := hb (x 10 4)
    have b15225 := hb (x 10 12)
    clear * - r15223 b15224 b15225 d15210
    omega
  have d15226 : (x 9 13).toNat = 0 := by
    have r15227 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15228 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e15229 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b15230 := hb (x 7 3)
    have b15231 := hb (x 8 2)
    have b15232 := hb (x 9 13)
    have b15233 := hb (x 10 12)
    clear * - r15227 e15228 e15229 b15230 b15231 b15232 b15233 d15210 d15117 d15206
    omega
  have d15234 : (x 9 2 && x 9 13).toNat = 0 := by
    have r15235 := hand2 (x 9 2) (x 9 13)
    have b15236 := hb (x 9 13)
    have b15237 := hb (x 9 2 && x 9 13)
    clear * - r15235 b15236 b15237 d15226
    omega
  have d15238 : (x 9 5).toNat = 0 := by
    have r15239 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
    have b15240 := hb (x 9 5)
    have b15241 := hb (x 9 13)
    clear * - r15239 b15240 b15241 d15226
    omega
  have d15242 : (x 7 4).toNat = 0 := by
    have r15243 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15244 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e15245 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e15246 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e15247 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e15248 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e15249 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b15250 := hb (x 4 7)
    have b15251 := hb (x 5 6)
    have b15252 := hb (x 6 5)
    have b15253 := hb (x 7 4)
    have b15254 := hb (x 8 11)
    have b15255 := hb (x 9 10)
    have b15256 := hb (x 10 9)
    have b15257 := hb (x 11 8)
    clear * - r15243 e15244 e15245 e15246 e15247 e15248 e15249 b15250 b15251 b15252 b15253 b15254 b15255 b15256 b15257 d14826 d14850 d14874 d14902 d15047 d14815
    omega
  have d15258 : (x 7 4 && x 7 14).toNat = 0 := by
    have r15259 := hand1 (x 7 4) (x 7 14)
    have b15260 := hb (x 7 4)
    have b15261 := hb (x 7 4 && x 7 14)
    clear * - r15259 b15260 b15261 d15242
    omega
  have d15262 : (x 7 4 && x 7 13).toNat = 0 := by
    have r15263 := hand1 (x 7 4) (x 7 13)
    have b15264 := hb (x 7 4)
    have b15265 := hb (x 7 4 && x 7 13)
    clear * - r15263 b15264 b15265 d15242
    omega
  have d15266 : (x 7 4 && x 7 11).toNat = 0 := by
    have r15267 := hand1 (x 7 4) (x 7 11)
    have b15268 := hb (x 7 4)
    have b15269 := hb (x 7 4 && x 7 11)
    clear * - r15267 b15268 b15269 d15242
    omega
  have d15270 : (x 7 4 && x 7 10).toNat = 0 := by
    have r15271 := hand1 (x 7 4) (x 7 10)
    have b15272 := hb (x 7 4)
    have b15273 := hb (x 7 4 && x 7 10)
    clear * - r15271 b15272 b15273 d15242
    omega
  have d15274 : (x 11 11).toNat = 1 := by
    have r15275 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15276 := hb (x 7 4)
    have b15277 := hb (x 11 11)
    have b15278 := hb (x 10 1 && x 10 12)
    have b15279 := hb (x 9 2 && x 9 13)
    have b15280 := hb (x 8 3 && x 8 14)
    clear * - r15275 b15276 b15277 b15278 b15279 b15280 d15218 d15234 d15109 d15242
    omega
  have d15281 : (x 11 3).toNat = 1 := by
    have r15282 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
    have b15283 := hb (x 11 3)
    have b15284 := hb (x 11 11)
    clear * - r15282 b15283 b15284 d15274
    omega
  have d15285 : (x 14 12).toNat = 0 := by
    have r15286 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15287 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e15288 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b15289 := hb (x 11 3)
    have b15290 := hb (x 12 2)
    have b15291 := hb (x 13 13)
    have b15292 := hb (x 14 12)
    clear * - r15286 e15287 e15288 b15289 b15290 b15291 b15292 d15281
    omega
  have d15293 : (x 14 4).toNat = 0 := by
    have r15294 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
    have b15295 := hb (x 14 4)
    have b15296 := hb (x 14 12)
    clear * - r15294 b15295 b15296 d15285
    omega
  have d15297 : (x 14 4 && x 14 13).toNat = 0 := by
    have r15298 := hand1 (x 14 4) (x 14 13)
    have b15299 := hb (x 14 4)
    have b15300 := hb (x 14 4 && x 14 13)
    clear * - r15298 b15299 b15300 d15293
    omega
  have d15301 : (x 13 13).toNat = 0 := by
    have r15302 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15303 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e15304 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b15305 := hb (x 11 3)
    have b15306 := hb (x 12 2)
    have b15307 := hb (x 13 13)
    have b15308 := hb (x 14 12)
    clear * - r15302 e15303 e15304 b15305 b15306 b15307 b15308 d15285 d15281
    omega
  have d15309 : (x 13 5).toNat = 0 := by
    have r15310 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
    have b15311 := hb (x 13 5)
    have b15312 := hb (x 13 13)
    clear * - r15310 b15311 b15312 d15301
    omega
  have d15313 : (x 13 5 && x 13 14).toNat = 0 := by
    have r15314 := hand1 (x 13 5) (x 13 14)
    have b15315 := hb (x 13 5)
    have b15316 := hb (x 13 5 && x 13 14)
    clear * - r15314 b15315 b15316 d15309
    omega
  have d15317 : (x 12 2).toNat = 0 := by
    have r15318 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15319 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e15320 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b15321 := hb (x 11 3)
    have b15322 := hb (x 12 2)
    have b15323 := hb (x 13 13)
    have b15324 := hb (x 14 12)
    clear * - r15318 e15319 e15320 b15321 b15322 b15323 b15324 d15285 d15301 d15281
    omega
  have d15325 : (x 12 10).toNat = 0 := by
    have r15326 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
    have b15327 := hb (x 12 2)
    have b15328 := hb (x 12 10)
    clear * - r15326 b15327 b15328 d15317
    omega
  have d15329 : (x 14 8).toNat = 0 := by
    have r15330 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15331 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e15332 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e15333 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e15334 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e15335 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e15336 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b15337 := hb (x 7 7)
    have b15338 := hb (x 8 6)
    have b15339 := hb (x 9 5)
    have b15340 := hb (x 10 4)
    have b15341 := hb (x 11 11)
    have b15342 := hb (x 12 10)
    have b15343 := hb (x 13 9)
    have b15344 := hb (x 14 8)
    clear * - r15330 e15331 e15332 e15333 e15334 e15335 e15336 b15337 b15338 b15339 b15340 b15341 b15342 b15343 b15344 d15325 d15274 d15222 d15238 d15113
    omega
  have d15345 : (x 13 9).toNat = 0 := by
    have r15346 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15347 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e15348 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e15349 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e15350 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e15351 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e15352 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b15353 := hb (x 7 7)
    have b15354 := hb (x 8 6)
    have b15355 := hb (x 9 5)
    have b15356 := hb (x 10 4)
    have b15357 := hb (x 11 11)
    have b15358 := hb (x 12 10)
    have b15359 := hb (x 13 9)
    have b15360 := hb (x 14 8)
    clear * - r15346 e15347 e15348 e15349 e15350 e15351 e15352 b15353 b15354 b15355 b15356 b15357 b15358 b15359 b15360 d15329 d15325 d15274 d15222 d15238 d15113
    omega
  have d15361 : (x 7 7).toNat = 0 := by
    have r15362 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15363 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e15364 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e15365 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e15366 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e15367 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e15368 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b15369 := hb (x 7 7)
    have b15370 := hb (x 8 6)
    have b15371 := hb (x 9 5)
    have b15372 := hb (x 10 4)
    have b15373 := hb (x 11 11)
    have b15374 := hb (x 12 10)
    have b15375 := hb (x 13 9)
    have b15376 := hb (x 14 8)
    clear * - r15362 e15363 e15364 e15365 e15366 e15367 e15368 b15369 b15370 b15371 b15372 b15373 b15374 b15375 b15376 d15329 d15345 d15325 d15274 d15222 d15238 d15113
    omega
  have d15377 : (x 7 1 && x 7 7).toNat = 0 := by
    have r15378 := hand2 (x 7 1) (x 7 7)
    have b15379 := hb (x 7 7)
    have b15380 := hb (x 7 1 && x 7 7)
    clear * - r15378 b15379 b15380 d15361
    omega
  have d15381 : (x 5 6).toNat = 0 := by
    have r15382 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15383 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e15384 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e15385 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e15386 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e15387 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e15388 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b15389 := hb (x 4 7)
    have b15390 := hb (x 5 6)
    have b15391 := hb (x 6 5)
    have b15392 := hb (x 7 4)
    have b15393 := hb (x 8 11)
    have b15394 := hb (x 9 10)
    have b15395 := hb (x 10 9)
    have b15396 := hb (x 11 8)
    clear * - r15382 e15383 e15384 e15385 e15386 e15387 e15388 b15389 b15390 b15391 b15392 b15393 b15394 b15395 b15396 d14826 d14850 d14874 d14902 d15242 d15047 d14815
    omega
  have d15397 : (x 3 5 && x 3 11).toNat = 1 := by
    have r15398 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15399 := hb (x (-1) 9)
    have b15400 := hb (x 8 6)
    have b15401 := hb (x 7 1 && x 7 7)
    have b15402 := hb (x 6 2 && x 6 8)
    have b15403 := hb (x 5 3 && x 5 9)
    have b15404 := hb (x 4 4 && x 4 10)
    have b15405 := hb (x 3 5 && x 3 11)
    have b15406 := hb (x 2 6 && x 2 12)
    have b15407 := hb (x 1 7 && x 1 13)
    have b15408 := hb (x 0 8 && x 0 14)
    clear * - r15398 b15399 b15400 b15401 b15402 b15403 b15404 b15405 b15406 b15407 b15408 d15113 d15377 d14525 d14545 d14430 d14077 d14097 d14751 d14052
    omega
  have d15409 : (x 3 5).toNat = 1 := by
    have r15410 := hand1 (x 3 5) (x 3 11)
    have b15411 := hb (x 3 5)
    have b15412 := hb (x 3 5 && x 3 11)
    clear * - r15410 b15411 b15412 d15397
    omega
  have d15413 : (x 8 8).toNat = 0 := by
    have r15414 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15415 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e15416 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e15417 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e15418 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e15419 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e15420 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b15421 := hb (x 1 7)
    have b15422 := hb (x 2 6)
    have b15423 := hb (x 3 5)
    have b15424 := hb (x 4 4)
    have b15425 := hb (x 5 11)
    have b15426 := hb (x 6 10)
    have b15427 := hb (x 7 9)
    have b15428 := hb (x 8 8)
    clear * - r15414 e15415 e15416 e15417 e15418 e15419 e15420 b15421 b15422 b15423 b15424 b15425 b15426 b15427 b15428 d15092 d15190 d14611 d15409
    omega
  have d15429 : (x 7 9).toNat = 0 := by
    have r15430 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15431 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e15432 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e15433 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e15434 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e15435 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e15436 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b15437 := hb (x 1 7)
    have b15438 := hb (x 2 6)
    have b15439 := hb (x 3 5)
    have b15440 := hb (x 4 4)
    have b15441 := hb (x 5 11)
    have b15442 := hb (x 6 10)
    have b15443 := hb (x 7 9)
    have b15444 := hb (x 8 8)
    clear * - r15430 e15431 e15432 e15433 e15434 e15435 e15436 b15437 b15438 b15439 b15440 b15441 b15442 b15443 b15444 d15413 d15092 d15190 d14611 d15409
    omega
  have d15445 : (x 3 4 && x 3 13).toNat = 1 := by
    have r15446 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15447 := hb (x 1 6)
    have b15448 := hb (x 7 9)
    have b15449 := hb (x 6 1 && x 6 10)
    have b15450 := hb (x 5 2 && x 5 11)
    have b15451 := hb (x 4 3 && x 4 12)
    have b15452 := hb (x 3 4 && x 3 13)
    have b15453 := hb (x 2 5 && x 2 14)
    clear * - r15446 b15447 b15448 b15449 b15450 b15451 b15452 b15453 d15429 d14975 d15145 d14607 d14651 g9
    omega
  have d15454 : (x 3 4).toNat = 1 := by
    have r15455 := hand1 (x 3 4) (x 3 13)
    have b15456 := hb (x 3 4)
    have b15457 := hb (x 3 4 && x 3 13)
    clear * - r15455 b15456 b15457 d15445
    omega
  have d15458 : (x 7 8).toNat = 0 := by
    have r15459 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15460 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15461 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15462 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15463 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15464 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15465 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15466 := hb (x 0 7)
    have b15467 := hb (x 1 6)
    have b15468 := hb (x 2 5)
    have b15469 := hb (x 3 4)
    have b15470 := hb (x 4 11)
    have b15471 := hb (x 5 10)
    have b15472 := hb (x 6 9)
    have b15473 := hb (x 7 8)
    clear * - r15459 e15460 e15461 e15462 e15463 e15464 e15465 b15466 b15467 b15468 b15469 b15470 b15471 b15472 b15473 d14983 d15153 d15202 d15454 d14647 g9
    omega
  have d15474 : (x 0 7).toNat = 0 := by
    have r15475 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15476 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e15477 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e15478 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e15479 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e15480 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e15481 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b15482 := hb (x 0 7)
    have b15483 := hb (x 1 6)
    have b15484 := hb (x 2 5)
    have b15485 := hb (x 3 4)
    have b15486 := hb (x 4 11)
    have b15487 := hb (x 5 10)
    have b15488 := hb (x 6 9)
    have b15489 := hb (x 7 8)
    clear * - r15475 e15476 e15477 e15478 e15479 e15480 e15481 b15482 b15483 b15484 b15485 b15486 b15487 b15488 b15489 d15458 d14983 d15153 d15202 d15454 d14647 g9
    omega
  have d15490 : (x 0 7 && x 0 13).toNat = 0 := by
    have r15491 := hand1 (x 0 7) (x 0 13)
    have b15492 := hb (x 0 7)
    have b15493 := hb (x 0 7 && x 0 13)
    clear * - r15491 b15492 b15493 d15474
    omega
  have d15494 : (x (-8) 8).toNat = 1 := by
    have r15495 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15496 := hb (x (-8) 8)
    have b15497 := hb (x 0 7)
    have b15498 := hb (x (-1) 1 && x (-1) 8)
    have b15499 := hb (x (-2) 2 && x (-2) 9)
    have b15500 := hb (x (-3) 3 && x (-3) 10)
    have b15501 := hb (x (-4) 4 && x (-4) 11)
    have b15502 := hb (x (-5) 5 && x (-5) 12)
    have b15503 := hb (x (-6) 6 && x (-6) 13)
    have b15504 := hb (x (-7) 7 && x (-7) 14)
    clear * - r15495 b15496 b15497 b15498 b15499 b15500 b15501 b15502 b15503 b15504 d15474 d14048 g19 g20 d14450 d14168 d14771 d14791
    omega
  have d15505 : (x (-9) 9).toNat = 0 := by
    have r15506 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15507 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
    have e15508 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
    have e15509 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
    have e15510 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
    have e15511 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
    have e15512 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
    have b15513 := hb (x (-15) 7)
    have b15514 := hb (x (-14) 6)
    have b15515 := hb (x (-13) 5)
    have b15516 := hb (x (-12) 4)
    have b15517 := hb (x (-11) 11)
    have b15518 := hb (x (-10) 10)
    have b15519 := hb (x (-9) 9)
    have b15520 := hb (x (-8) 8)
    clear * - r15506 e15507 e15508 e15509 e15510 e15511 e15512 b15513 b15514 b15515 b15516 b15517 b15518 b15519 b15520 d15494 d14489 d14505
    omega
  have d15521 : (x (-12) 4).toNat = 0 := by
    have r15522 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15523 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
    have e15524 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
    have e15525 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
    have e15526 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
    have e15527 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
    have e15528 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
    have b15529 := hb (x (-15) 7)
    have b15530 := hb (x (-14) 6)
    have b15531 := hb (x (-13) 5)
    have b15532 := hb (x (-12) 4)
    have b15533 := hb (x (-11) 11)
    have b15534 := hb (x (-10) 10)
    have b15535 := hb (x (-9) 9)
    have b15536 := hb (x (-8) 8)
    clear * - r15522 e15523 e15524 e15525 e15526 e15527 e15528 b15529 b15530 b15531 b15532 b15533 b15534 b15535 b15536 d15494 d15505 d14489 d14505
    omega
  have d15537 : (x 3 1 && x 3 7).toNat = 1 := by
    have r15538 : 1 ≤ (x 4 6).toNat + (x 3 1 && x 3 7).toNat + (x 2 2 && x 2 8).toNat + (x 1 3 && x 1 9).toNat + (x 0 4 && x 0 10).toNat + (x (-1) 5 && x (-1) 11).toNat + (x (-2) 6 && x (-2) 12).toNat + (x (-3) 7 && x (-3) 13).toNat + (x (-4) 8 && x (-4) 14).toNat + (x (-5) 9).toNat := by have q := hcov6 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15539 := hb (x (-5) 9)
    have b15540 := hb (x 4 6)
    have b15541 := hb (x 3 1 && x 3 7)
    have b15542 := hb (x 2 2 && x 2 8)
    have b15543 := hb (x 1 3 && x 1 9)
    have b15544 := hb (x 0 4 && x 0 10)
    have b15545 := hb (x (-1) 5 && x (-1) 11)
    have b15546 := hb (x (-2) 6 && x (-2) 12)
    have b15547 := hb (x (-3) 7 && x (-3) 13)
    have b15548 := hb (x (-4) 8 && x (-4) 14)
    clear * - r15538 b15539 b15540 b15541 b15542 b15543 b15544 b15545 b15546 b15547 b15548 d14595 d14627 d14639 g13 g14 g15 g16 d14811 d14314
    omega
  have d15549 : (x 3 7).toNat = 1 := by
    have r15550 := hand2 (x 3 1) (x 3 7)
    have b15551 := hb (x 3 7)
    have b15552 := hb (x 3 1 && x 3 7)
    clear * - r15550 b15551 b15552 d15537
    omega
  have d15553 : (x 10 8).toNat = 0 := by
    have r15554 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15555 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e15556 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e15557 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e15558 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e15559 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e15560 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have b15561 := hb (x 3 7)
    have b15562 := hb (x 4 6)
    have b15563 := hb (x 5 5)
    have b15564 := hb (x 6 4)
    have b15565 := hb (x 7 11)
    have b15566 := hb (x 8 10)
    have b15567 := hb (x 9 9)
    have b15568 := hb (x 10 8)
    clear * - r15554 e15555 e15556 e15557 e15558 e15559 e15560 b15561 b15562 b15563 b15564 b15565 b15566 b15567 b15568 d15121 d14378 d14406 d14595 d15549
    omega
  have d15569 : (x 10 1 && x 10 8).toNat = 0 := by
    have r15570 := hand2 (x 10 1) (x 10 8)
    have b15571 := hb (x 10 8)
    have b15572 := hb (x 10 1 && x 10 8)
    clear * - r15570 b15571 b15572 d15553
    omega
  have d15573 : (x 10 2 && x 10 8).toNat = 0 := by
    have r15574 := hand2 (x 10 2) (x 10 8)
    have b15575 := hb (x 10 8)
    have b15576 := hb (x 10 2 && x 10 8)
    clear * - r15574 b15575 b15576 d15553
    omega
  have d15577 : (x 9 9).toNat = 0 := by
    have r15578 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15579 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e15580 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e15581 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e15582 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e15583 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e15584 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have b15585 := hb (x 3 7)
    have b15586 := hb (x 4 6)
    have b15587 := hb (x 5 5)
    have b15588 := hb (x 6 4)
    have b15589 := hb (x 7 11)
    have b15590 := hb (x 8 10)
    have b15591 := hb (x 9 9)
    have b15592 := hb (x 10 8)
    clear * - r15578 e15579 e15580 e15581 e15582 e15583 e15584 b15585 b15586 b15587 b15588 b15589 b15590 b15591 b15592 d15553 d15121 d14378 d14406 d14595 d15549
    omega
  have d15593 : (x 9 2 && x 9 9).toNat = 0 := by
    have r15594 := hand2 (x 9 2) (x 9 9)
    have b15595 := hb (x 9 9)
    have b15596 := hb (x 9 2 && x 9 9)
    clear * - r15594 b15595 b15596 d15577
    omega
  have d15597 : (x 11 7).toNat = 1 := by
    have r15598 : 1 ≤ (x 11 7).toNat + (x 10 1 && x 10 8).toNat + (x 9 2 && x 9 9).toNat + (x 8 3 && x 8 10).toNat + (x 7 4 && x 7 11).toNat + (x 6 5 && x 6 12).toNat + (x 5 6 && x 5 13).toNat + (x 4 7 && x 4 14).toNat + (x 3 8).toNat := by have q := hcov7 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15599 := hb (x 3 8)
    have b15600 := hb (x 11 7)
    have b15601 := hb (x 10 1 && x 10 8)
    have b15602 := hb (x 9 2 && x 9 9)
    have b15603 := hb (x 8 3 && x 8 10)
    have b15604 := hb (x 7 4 && x 7 11)
    have b15605 := hb (x 6 5 && x 6 12)
    have b15606 := hb (x 5 6 && x 5 13)
    have b15607 := hb (x 4 7 && x 4 14)
    clear * - r15598 b15599 b15600 b15601 b15602 b15603 b15604 b15605 b15606 b15607 d15569 d15593 d15129 d15266 d14370 d14398 d14591 d14711
    omega
  have d15608 : (x 18 8).toNat = 0 := by
    have r15609 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15610 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
    have e15611 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
    have e15612 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
    have e15613 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
    have e15614 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
    have e15615 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
    have b15616 := hb (x 11 7)
    have b15617 := hb (x 12 6)
    have b15618 := hb (x 13 5)
    have b15619 := hb (x 14 4)
    have b15620 := hb (x 15 11)
    have b15621 := hb (x 16 10)
    have b15622 := hb (x 17 9)
    have b15623 := hb (x 18 8)
    clear * - r15609 e15610 e15611 e15612 e15613 e15614 e15615 b15616 b15617 b15618 b15619 b15620 b15621 b15622 b15623 d15293 d15309 d15597
    omega
  have d15624 : (x 17 9).toNat = 0 := by
    have r15625 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15626 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
    have e15627 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
    have e15628 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
    have e15629 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
    have e15630 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
    have e15631 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
    have b15632 := hb (x 11 7)
    have b15633 := hb (x 12 6)
    have b15634 := hb (x 13 5)
    have b15635 := hb (x 14 4)
    have b15636 := hb (x 15 11)
    have b15637 := hb (x 16 10)
    have b15638 := hb (x 17 9)
    have b15639 := hb (x 18 8)
    clear * - r15625 e15626 e15627 e15628 e15629 e15630 e15631 b15632 b15633 b15634 b15635 b15636 b15637 b15638 b15639 d15608 d15293 d15309 d15597
    omega
  have d15640 : (x 16 10).toNat = 0 := by
    have r15641 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15642 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
    have e15643 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
    have e15644 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
    have e15645 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
    have e15646 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
    have e15647 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
    have b15648 := hb (x 11 7)
    have b15649 := hb (x 12 6)
    have b15650 := hb (x 13 5)
    have b15651 := hb (x 14 4)
    have b15652 := hb (x 15 11)
    have b15653 := hb (x 16 10)
    have b15654 := hb (x 17 9)
    have b15655 := hb (x 18 8)
    clear * - r15641 e15642 e15643 e15644 e15645 e15646 e15647 b15648 b15649 b15650 b15651 b15652 b15653 b15654 b15655 d15608 d15624 d15293 d15309 d15597
    omega
  have d15656 : (x 15 11).toNat = 0 := by
    have r15657 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15658 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
    have e15659 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
    have e15660 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
    have e15661 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
    have e15662 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
    have e15663 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
    have b15664 := hb (x 11 7)
    have b15665 := hb (x 12 6)
    have b15666 := hb (x 13 5)
    have b15667 := hb (x 14 4)
    have b15668 := hb (x 15 11)
    have b15669 := hb (x 16 10)
    have b15670 := hb (x 17 9)
    have b15671 := hb (x 18 8)
    clear * - r15657 e15658 e15659 e15660 e15661 e15662 e15663 b15664 b15665 b15666 b15667 b15668 b15669 b15670 b15671 d15608 d15624 d15640 d15293 d15309 d15597
    omega
  have d15672 : (x 12 6).toNat = 0 := by
    have r15673 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15674 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
    have e15675 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
    have e15676 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
    have e15677 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
    have e15678 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
    have e15679 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
    have b15680 := hb (x 11 7)
    have b15681 := hb (x 12 6)
    have b15682 := hb (x 13 5)
    have b15683 := hb (x 14 4)
    have b15684 := hb (x 15 11)
    have b15685 := hb (x 16 10)
    have b15686 := hb (x 17 9)
    have b15687 := hb (x 18 8)
    clear * - r15673 e15674 e15675 e15676 e15677 e15678 e15679 b15680 b15681 b15682 b15683 b15684 b15685 b15686 b15687 d15608 d15624 d15640 d15656 d15293 d15309 d15597
    omega
  have d15688 : (x 9 3 && x 9 9).toNat = 0 := by
    have r15689 := hand2 (x 9 3) (x 9 9)
    have b15690 := hb (x 9 9)
    have b15691 := hb (x 9 3 && x 9 9)
    clear * - r15689 b15690 b15691 d15577
    omega
  have d15692 : (x 7 11).toNat = 0 := by
    have r15693 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15694 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e15695 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e15696 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e15697 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e15698 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e15699 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have b15700 := hb (x 3 7)
    have b15701 := hb (x 4 6)
    have b15702 := hb (x 5 5)
    have b15703 := hb (x 6 4)
    have b15704 := hb (x 7 11)
    have b15705 := hb (x 8 10)
    have b15706 := hb (x 9 9)
    have b15707 := hb (x 10 8)
    clear * - r15693 e15694 e15695 e15696 e15697 e15698 e15699 b15700 b15701 b15702 b15703 b15704 b15705 b15706 b15707 d15553 d15577 d15121 d14378 d14406 d14595 d15549
    omega
  have d15708 : (x 7 2 && x 7 11).toNat = 0 := by
    have r15709 := hand2 (x 7 2) (x 7 11)
    have b15710 := hb (x 7 11)
    have b15711 := hb (x 7 2 && x 7 11)
    clear * - r15709 b15710 b15711 d15692
    omega
  have d15712 : (x 3 6).toNat = 1 := by
    have r15713 : 1 ≤ (x 9 9).toNat + (x 8 1 && x 8 10).toNat + (x 7 2 && x 7 11).toNat + (x 6 3 && x 6 12).toNat + (x 5 4 && x 5 13).toNat + (x 4 5 && x 4 14).toNat + (x 3 6).toNat := by have q := hcov9 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15714 := hb (x 3 6)
    have b15715 := hb (x 9 9)
    have b15716 := hb (x 8 1 && x 8 10)
    have b15717 := hb (x 7 2 && x 7 11)
    have b15718 := hb (x 6 3 && x 6 12)
    have b15719 := hb (x 5 4 && x 5 13)
    have b15720 := hb (x 4 5 && x 4 14)
    clear * - r15713 b15714 b15715 b15716 b15717 b15718 b15719 b15720 d15577 d15125 d15708 d14366 d14394 d14587
    omega
  have d15721 : (x 9 8).toNat = 0 := by
    have r15722 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15723 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e15724 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e15725 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e15726 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e15727 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e15728 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b15729 := hb (x 2 7)
    have b15730 := hb (x 3 6)
    have b15731 := hb (x 4 5)
    have b15732 := hb (x 5 4)
    have b15733 := hb (x 6 11)
    have b15734 := hb (x 7 10)
    have b15735 := hb (x 8 9)
    have b15736 := hb (x 9 8)
    clear * - r15722 e15723 e15724 e15725 e15726 e15727 e15728 b15729 b15730 b15731 b15732 b15733 b15734 b15735 b15736 d15031 d14675 d14695 d15712
    omega
  have d15737 : (x 9 2 && x 9 8).toNat = 0 := by
    have r15738 := hand2 (x 9 2) (x 9 8)
    have b15739 := hb (x 9 8)
    have b15740 := hb (x 9 2 && x 9 8)
    clear * - r15738 b15739 b15740 d15721
    omega
  have d15741 : (x 8 9).toNat = 0 := by
    have r15742 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15743 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e15744 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e15745 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e15746 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e15747 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e15748 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b15749 := hb (x 2 7)
    have b15750 := hb (x 3 6)
    have b15751 := hb (x 4 5)
    have b15752 := hb (x 5 4)
    have b15753 := hb (x 6 11)
    have b15754 := hb (x 7 10)
    have b15755 := hb (x 8 9)
    have b15756 := hb (x 9 8)
    clear * - r15742 e15743 e15744 e15745 e15746 e15747 e15748 b15749 b15750 b15751 b15752 b15753 b15754 b15755 b15756 d15721 d15031 d14675 d14695 d15712
    omega
  have d15757 : (x 8 3 && x 8 9).toNat = 0 := by
    have r15758 := hand2 (x 8 3) (x 8 9)
    have b15759 := hb (x 8 9)
    have b15760 := hb (x 8 3 && x 8 9)
    clear * - r15758 b15759 b15760 d15741
    omega
  have d15761 : (x 7 5 && x 7 11).toNat = 0 := by
    have r15762 := hand2 (x 7 5) (x 7 11)
    have b15763 := hb (x 7 11)
    have b15764 := hb (x 7 5 && x 7 11)
    clear * - r15762 b15763 b15764 d15692
    omega
  have d15765 : (x 11 1 && x 11 7).toNat = 1 := by
    have r15766 : 1 ≤ (x 12 6).toNat + (x 11 1 && x 11 7).toNat + (x 10 2 && x 10 8).toNat + (x 9 3 && x 9 9).toNat + (x 8 4 && x 8 10).toNat + (x 7 5 && x 7 11).toNat + (x 6 6 && x 6 12).toNat + (x 5 7 && x 5 13).toNat + (x 4 8 && x 4 14).toNat + (x 3 9).toNat := by have q := hcov6 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15767 := hb (x 3 9)
    have b15768 := hb (x 12 6)
    have b15769 := hb (x 11 1 && x 11 7)
    have b15770 := hb (x 10 2 && x 10 8)
    have b15771 := hb (x 9 3 && x 9 9)
    have b15772 := hb (x 8 4 && x 8 10)
    have b15773 := hb (x 7 5 && x 7 11)
    have b15774 := hb (x 6 6 && x 6 12)
    have b15775 := hb (x 5 7 && x 5 13)
    have b15776 := hb (x 4 8 && x 4 14)
    clear * - r15766 b15767 b15768 b15769 b15770 b15771 b15772 b15773 b15774 b15775 b15776 d15672 d15573 d15688 d15133 d15761 d14374 d14402 g18 g11
    omega
  have d15777 : (x 11 1).toNat = 1 := by
    have r15778 := hand1 (x 11 1) (x 11 7)
    have b15779 := hb (x 11 1)
    have b15780 := hb (x 11 1 && x 11 7)
    clear * - r15778 b15779 b15780 d15765
    omega
  have d15781 : (x 12 14).toNat = 0 := by
    have r15782 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15783 := hb (x 11 1)
    have b15784 := hb (x 12 14)
    clear * - r15782 b15783 b15784 d15777
    omega
  have d15785 : (x 12 1 && x 12 14).toNat = 0 := by
    have r15786 := hand2 (x 12 1) (x 12 14)
    have b15787 := hb (x 12 14)
    have b15788 := hb (x 12 1 && x 12 14)
    clear * - r15786 b15787 b15788 d15781
    omega
  have d15789 : (x 11 2).toNat = 1 := by
    have r15790 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15791 := hb (x 11 2)
    have b15792 := hb (x 13 13)
    have b15793 := hb (x 12 1 && x 12 14)
    clear * - r15790 b15791 b15792 b15793 d15301 d15785
    omega
  have d15794 : (x 11 14).toNat = 1 := by
    have r15795 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
    have b15796 := hb (x 11 2)
    have b15797 := hb (x 11 14)
    clear * - r15795 b15796 b15797 d15789
    omega
  have d15798 : (x 10 1).toNat = 0 := by
    have r15799 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15800 := hb (x 10 1)
    have b15801 := hb (x 11 14)
    clear * - r15799 b15800 b15801 d15794
    omega
  have d15802 : (x 10 1 && x 10 11).toNat = 0 := by
    have r15803 := hand1 (x 10 1) (x 10 11)
    have b15804 := hb (x 10 1)
    have b15805 := hb (x 10 1 && x 10 11)
    clear * - r15803 b15804 b15805 d15798
    omega
  have d15806 : (x 11 10).toNat = 1 := by
    have r15807 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15808 := hb (x 6 5)
    have b15809 := hb (x 11 10)
    have b15810 := hb (x 10 1 && x 10 11)
    have b15811 := hb (x 9 2 && x 9 12)
    have b15812 := hb (x 8 3 && x 8 13)
    have b15813 := hb (x 7 4 && x 7 14)
    clear * - r15807 b15808 b15809 b15810 b15811 b15812 b15813 d15802 d14995 d15011 d15258 d15047
    omega
  have d15814 : (x 13 8).toNat = 0 := by
    have r15815 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15816 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e15817 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e15818 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e15819 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e15820 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e15821 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b15822 := hb (x 6 7)
    have b15823 := hb (x 7 6)
    have b15824 := hb (x 8 5)
    have b15825 := hb (x 9 4)
    have b15826 := hb (x 10 11)
    have b15827 := hb (x 11 10)
    have b15828 := hb (x 12 9)
    have b15829 := hb (x 13 8)
    clear * - r15815 e15816 e15817 e15818 e15819 e15820 e15821 b15822 b15823 b15824 b15825 b15826 b15827 b15828 b15829 d15806 d14999 d15015
    omega
  have d15830 : (x 12 9).toNat = 0 := by
    have r15831 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15832 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e15833 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e15834 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e15835 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e15836 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e15837 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b15838 := hb (x 6 7)
    have b15839 := hb (x 7 6)
    have b15840 := hb (x 8 5)
    have b15841 := hb (x 9 4)
    have b15842 := hb (x 10 11)
    have b15843 := hb (x 11 10)
    have b15844 := hb (x 12 9)
    have b15845 := hb (x 13 8)
    clear * - r15831 e15832 e15833 e15834 e15835 e15836 e15837 b15838 b15839 b15840 b15841 b15842 b15843 b15844 b15845 d15814 d15806 d14999 d15015
    omega
  have d15846 : (x 10 11).toNat = 0 := by
    have r15847 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15848 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e15849 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e15850 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e15851 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e15852 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e15853 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b15854 := hb (x 6 7)
    have b15855 := hb (x 7 6)
    have b15856 := hb (x 8 5)
    have b15857 := hb (x 9 4)
    have b15858 := hb (x 10 11)
    have b15859 := hb (x 11 10)
    have b15860 := hb (x 12 9)
    have b15861 := hb (x 13 8)
    clear * - r15847 e15848 e15849 e15850 e15851 e15852 e15853 b15854 b15855 b15856 b15857 b15858 b15859 b15860 b15861 d15814 d15830 d15806 d14999 d15015
    omega
  have d15862 : (x 7 6).toNat = 0 := by
    have r15863 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15864 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e15865 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e15866 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e15867 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e15868 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e15869 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b15870 := hb (x 6 7)
    have b15871 := hb (x 7 6)
    have b15872 := hb (x 8 5)
    have b15873 := hb (x 9 4)
    have b15874 := hb (x 10 11)
    have b15875 := hb (x 11 10)
    have b15876 := hb (x 12 9)
    have b15877 := hb (x 13 8)
    clear * - r15863 e15864 e15865 e15866 e15867 e15868 e15869 b15870 b15871 b15872 b15873 b15874 b15875 b15876 b15877 d15814 d15830 d15806 d15846 d14999 d15015
    omega
  have d15878 : (x 7 6 && x 7 12).toNat = 0 := by
    have r15879 := hand1 (x 7 6) (x 7 12)
    have b15880 := hb (x 7 6)
    have b15881 := hb (x 7 6 && x 7 12)
    clear * - r15879 b15880 b15881 d15862
    omega
  have d15882 : (x 10 1 && x 10 10).toNat = 0 := by
    have r15883 := hand1 (x 10 1) (x 10 10)
    have b15884 := hb (x 10 1)
    have b15885 := hb (x 10 1 && x 10 10)
    clear * - r15883 b15884 b15885 d15798
    omega
  have d15886 : (x 10 1 && x 10 7).toNat = 0 := by
    have r15887 := hand1 (x 10 1) (x 10 7)
    have b15888 := hb (x 10 1)
    have b15889 := hb (x 10 1 && x 10 7)
    clear * - r15887 b15888 b15889 d15798
    omega
  have d15890 : (x 11 6).toNat = 1 := by
    have r15891 : 1 ≤ (x 11 6).toNat + (x 10 1 && x 10 7).toNat + (x 9 2 && x 9 8).toNat + (x 8 3 && x 8 9).toNat + (x 7 4 && x 7 10).toNat + (x 6 5 && x 6 11).toNat + (x 5 6 && x 5 12).toNat + (x 4 7 && x 4 13).toNat + (x 3 8 && x 3 14).toNat + (x 2 9).toNat := by have q := hcov6 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15892 := hb (x 2 9)
    have b15893 := hb (x 11 6)
    have b15894 := hb (x 10 1 && x 10 7)
    have b15895 := hb (x 9 2 && x 9 8)
    have b15896 := hb (x 8 3 && x 8 9)
    have b15897 := hb (x 7 4 && x 7 10)
    have b15898 := hb (x 6 5 && x 6 11)
    have b15899 := hb (x 5 6 && x 5 12)
    have b15900 := hb (x 4 7 && x 4 13)
    have b15901 := hb (x 3 8 && x 3 14)
    clear * - r15891 b15892 b15893 b15894 b15895 b15896 b15897 b15898 b15899 b15900 b15901 d15886 d15737 d15757 d15270 d15035 d14671 d14691 d14731 d14659
    omega
  have d15902 : (x 17 8).toNat = 0 := by
    have r15903 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15904 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e15905 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e15906 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e15907 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e15908 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e15909 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b15910 := hb (x 10 7)
    have b15911 := hb (x 11 6)
    have b15912 := hb (x 12 5)
    have b15913 := hb (x 13 4)
    have b15914 := hb (x 14 11)
    have b15915 := hb (x 15 10)
    have b15916 := hb (x 16 9)
    have b15917 := hb (x 17 8)
    clear * - r15903 e15904 e15905 e15906 e15907 e15908 e15909 b15910 b15911 b15912 b15913 b15914 b15915 b15916 b15917 d15890
    omega
  have d15918 : (x 16 9).toNat = 0 := by
    have r15919 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15920 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e15921 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e15922 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e15923 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e15924 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e15925 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b15926 := hb (x 10 7)
    have b15927 := hb (x 11 6)
    have b15928 := hb (x 12 5)
    have b15929 := hb (x 13 4)
    have b15930 := hb (x 14 11)
    have b15931 := hb (x 15 10)
    have b15932 := hb (x 16 9)
    have b15933 := hb (x 17 8)
    clear * - r15919 e15920 e15921 e15922 e15923 e15924 e15925 b15926 b15927 b15928 b15929 b15930 b15931 b15932 b15933 d15902 d15890
    omega
  have d15934 : (x 15 10).toNat = 0 := by
    have r15935 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15936 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e15937 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e15938 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e15939 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e15940 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e15941 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b15942 := hb (x 10 7)
    have b15943 := hb (x 11 6)
    have b15944 := hb (x 12 5)
    have b15945 := hb (x 13 4)
    have b15946 := hb (x 14 11)
    have b15947 := hb (x 15 10)
    have b15948 := hb (x 16 9)
    have b15949 := hb (x 17 8)
    clear * - r15935 e15936 e15937 e15938 e15939 e15940 e15941 b15942 b15943 b15944 b15945 b15946 b15947 b15948 b15949 d15902 d15918 d15890
    omega
  have d15950 : (x 14 11).toNat = 0 := by
    have r15951 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e15952 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e15953 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e15954 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e15955 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e15956 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e15957 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b15958 := hb (x 10 7)
    have b15959 := hb (x 11 6)
    have b15960 := hb (x 12 5)
    have b15961 := hb (x 13 4)
    have b15962 := hb (x 14 11)
    have b15963 := hb (x 15 10)
    have b15964 := hb (x 16 9)
    have b15965 := hb (x 17 8)
    clear * - r15951 e15952 e15953 e15954 e15955 e15956 e15957 b15958 b15959 b15960 b15961 b15962 b15963 b15964 b15965 d15902 d15918 d15934 d15890
    omega
  have d15966 : (x 14 1 && x 14 11).toNat = 0 := by
    have r15967 := hand2 (x 14 1) (x 14 11)
    have b15968 := hb (x 14 11)
    have b15969 := hb (x 14 1 && x 14 11)
    clear * - r15967 b15968 b15969 d15950
    omega
  have d15970 : (x 10 13).toNat = 0 := by
    have r15971 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
    have b15972 := hb (x 10 1)
    have b15973 := hb (x 10 13)
    clear * - r15971 b15972 b15973 d15798
    omega
  have d15974 : (x 10 5).toNat = 0 := by
    have r15975 : (x 10 5).toNat ≤ (x 10 13).toNat := himp _ _ (hp5 10)
    have b15976 := hb (x 10 5)
    have b15977 := hb (x 10 13)
    clear * - r15975 b15976 b15977 d15970
    omega
  have d15978 : (x 9 1 && x 9 14).toNat = 1 := by
    have r15979 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15980 := hb (x 8 2)
    have b15981 := hb (x 10 13)
    have b15982 := hb (x 9 1 && x 9 14)
    clear * - r15979 b15980 b15981 b15982 d15970 d15117
    omega
  have d15983 : (x 9 1).toNat = 1 := by
    have r15984 := hand1 (x 9 1) (x 9 14)
    have b15985 := hb (x 9 1)
    have b15986 := hb (x 9 1 && x 9 14)
    clear * - r15984 b15985 b15986 d15978
    omega
  have d15987 : (x 10 14).toNat = 0 := by
    have r15988 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b15989 := hb (x 9 1)
    have b15990 := hb (x 10 14)
    clear * - r15988 b15989 b15990 d15983
    omega
  have d15991 : (x 10 2).toNat = 0 := by
    have r15992 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
    have b15993 := hb (x 10 2)
    have b15994 := hb (x 10 14)
    clear * - r15992 b15993 b15994 d15987
    omega
  have d15995 : (x 10 10).toNat = 0 := by
    have r15996 : (x 10 10).toNat ≤ (x 10 2).toNat := himp _ _ (hp10 10)
    have b15997 := hb (x 10 2)
    have b15998 := hb (x 10 10)
    clear * - r15996 b15997 b15998 d15991
    omega
  have d15999 : (x 13 12).toNat = 0 := by
    have r16000 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16001 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e16002 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b16003 := hb (x 10 3)
    have b16004 := hb (x 11 2)
    have b16005 := hb (x 12 13)
    have b16006 := hb (x 13 12)
    clear * - r16000 e16001 e16002 b16003 b16004 b16005 b16006 d15789
    omega
  have d16007 : (x 13 2 && x 13 12).toNat = 0 := by
    have r16008 := hand2 (x 13 2) (x 13 12)
    have b16009 := hb (x 13 12)
    have b16010 := hb (x 13 2 && x 13 12)
    clear * - r16008 b16009 b16010 d15999
    omega
  have d16011 : (x 12 13).toNat = 0 := by
    have r16012 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16013 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e16014 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b16015 := hb (x 10 3)
    have b16016 := hb (x 11 2)
    have b16017 := hb (x 12 13)
    have b16018 := hb (x 13 12)
    clear * - r16012 e16013 e16014 b16015 b16016 b16017 b16018 d15999 d15789
    omega
  have d16019 : (x 12 3 && x 12 13).toNat = 0 := by
    have r16020 := hand2 (x 12 3) (x 12 13)
    have b16021 := hb (x 12 13)
    have b16022 := hb (x 12 3 && x 12 13)
    clear * - r16020 b16021 b16022 d16011
    omega
  have d16023 : (x 11 4 && x 11 14).toNat = 1 := by
    have r16024 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16025 := hb (x 10 5)
    have b16026 := hb (x 15 10)
    have b16027 := hb (x 14 1 && x 14 11)
    have b16028 := hb (x 13 2 && x 13 12)
    have b16029 := hb (x 12 3 && x 12 13)
    have b16030 := hb (x 11 4 && x 11 14)
    clear * - r16024 b16025 b16026 b16027 b16028 b16029 b16030 d15934 d15966 d16007 d16019 d15974
    omega
  have d16031 : (x 11 4).toNat = 1 := by
    have r16032 := hand1 (x 11 4) (x 11 14)
    have b16033 := hb (x 11 4)
    have b16034 := hb (x 11 4 && x 11 14)
    clear * - r16032 b16033 b16034 d16023
    omega
  have d16035 : (x 11 12).toNat = 1 := by
    have r16036 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
    have b16037 := hb (x 11 4)
    have b16038 := hb (x 11 12)
    clear * - r16036 b16037 b16038 d16031
    omega
  have d16039 : (x 9 2).toNat = 0 := by
    have r16040 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16041 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e16042 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b16043 := hb (x 8 3)
    have b16044 := hb (x 9 2)
    have b16045 := hb (x 10 13)
    have b16046 := hb (x 11 12)
    clear * - r16040 e16041 e16042 b16043 b16044 b16045 b16046 d16035 d15970
    omega
  have d16047 : (x 9 2 && x 9 11).toNat = 0 := by
    have r16048 := hand1 (x 9 2) (x 9 11)
    have b16049 := hb (x 9 2)
    have b16050 := hb (x 9 2 && x 9 11)
    clear * - r16048 b16049 b16050 d16039
    omega
  have d16051 : (x 11 9).toNat = 1 := by
    have r16052 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16053 := hb (x 5 6)
    have b16054 := hb (x 11 9)
    have b16055 := hb (x 10 1 && x 10 10)
    have b16056 := hb (x 9 2 && x 9 11)
    have b16057 := hb (x 8 3 && x 8 12)
    have b16058 := hb (x 7 4 && x 7 13)
    have b16059 := hb (x 6 5 && x 6 14)
    clear * - r16052 b16053 b16054 b16055 b16056 b16057 b16058 b16059 d15882 d16047 d15170 d15262 d15051 d15381
    omega
  have d16060 : (x 12 8).toNat = 0 := by
    have r16061 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16062 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e16063 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e16064 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e16065 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e16066 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e16067 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b16068 := hb (x 5 7)
    have b16069 := hb (x 6 6)
    have b16070 := hb (x 7 5)
    have b16071 := hb (x 8 4)
    have b16072 := hb (x 9 11)
    have b16073 := hb (x 10 10)
    have b16074 := hb (x 11 9)
    have b16075 := hb (x 12 8)
    clear * - r16061 e16062 e16063 e16064 e16065 e16066 e16067 b16068 b16069 b16070 b16071 b16072 b16073 b16074 b16075 d16051 d15995 d15174 d15084
    omega
  have d16076 : (x 9 11).toNat = 0 := by
    have r16077 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16078 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e16079 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e16080 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e16081 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e16082 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e16083 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b16084 := hb (x 5 7)
    have b16085 := hb (x 6 6)
    have b16086 := hb (x 7 5)
    have b16087 := hb (x 8 4)
    have b16088 := hb (x 9 11)
    have b16089 := hb (x 10 10)
    have b16090 := hb (x 11 9)
    have b16091 := hb (x 12 8)
    clear * - r16077 e16078 e16079 e16080 e16081 e16082 e16083 b16084 b16085 b16086 b16087 b16088 b16089 b16090 b16091 d16060 d16051 d15995 d15174 d15084
    omega
  have d16092 : (x 7 5).toNat = 0 := by
    have r16093 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16094 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e16095 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e16096 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e16097 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e16098 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e16099 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b16100 := hb (x 5 7)
    have b16101 := hb (x 6 6)
    have b16102 := hb (x 7 5)
    have b16103 := hb (x 8 4)
    have b16104 := hb (x 9 11)
    have b16105 := hb (x 10 10)
    have b16106 := hb (x 11 9)
    have b16107 := hb (x 12 8)
    clear * - r16093 e16094 e16095 e16096 e16097 e16098 e16099 b16100 b16101 b16102 b16103 b16104 b16105 b16106 b16107 d16060 d16051 d15995 d16076 d15174 d15084
    omega
  have d16108 : (x 7 5 && x 7 12).toNat = 0 := by
    have r16109 := hand1 (x 7 5) (x 7 12)
    have b16110 := hb (x 7 5)
    have b16111 := hb (x 7 5 && x 7 12)
    clear * - r16109 b16110 b16111 d16092
    omega
  have d16112 : (x 5 7).toNat = 0 := by
    have r16113 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16114 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e16115 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e16116 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e16117 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e16118 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e16119 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b16120 := hb (x 5 7)
    have b16121 := hb (x 6 6)
    have b16122 := hb (x 7 5)
    have b16123 := hb (x 8 4)
    have b16124 := hb (x 9 11)
    have b16125 := hb (x 10 10)
    have b16126 := hb (x 11 9)
    have b16127 := hb (x 12 8)
    clear * - r16113 e16114 e16115 e16116 e16117 e16118 e16119 b16120 b16121 b16122 b16123 b16124 b16125 b16126 b16127 d16060 d16051 d15995 d16076 d15174 d16092 d15084
    omega
  have d16128 : (x 5 7 && x 5 14).toNat = 0 := by
    have r16129 := hand1 (x 5 7) (x 5 14)
    have b16130 := hb (x 5 7)
    have b16131 := hb (x 5 7 && x 5 14)
    clear * - r16129 b16130 b16131 d16112
    omega
  have d16132 : (x 12 7).toNat = 1 := by
    have r16133 : 1 ≤ (x 12 7).toNat + (x 11 1 && x 11 8).toNat + (x 10 2 && x 10 9).toNat + (x 9 3 && x 9 10).toNat + (x 8 4 && x 8 11).toNat + (x 7 5 && x 7 12).toNat + (x 6 6 && x 6 13).toNat + (x 5 7 && x 5 14).toNat + (x 4 8).toNat := by have q := hcov7 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16134 := hb (x 4 8)
    have b16135 := hb (x 12 7)
    have b16136 := hb (x 11 1 && x 11 8)
    have b16137 := hb (x 10 2 && x 10 9)
    have b16138 := hb (x 9 3 && x 9 10)
    have b16139 := hb (x 8 4 && x 8 11)
    have b16140 := hb (x 7 5 && x 7 12)
    have b16141 := hb (x 6 6 && x 6 13)
    have b16142 := hb (x 5 7 && x 5 14)
    clear * - r16133 b16134 b16135 b16136 b16137 b16138 b16139 b16140 b16141 b16142 d14842 d14866 d14894 d15178 d16108 d15039 d16128 g12
    omega
  have d16143 : (x 19 8).toNat = 0 := by
    have r16144 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16145 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e16146 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e16147 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e16148 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e16149 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e16150 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b16151 := hb (x 12 7)
    have b16152 := hb (x 13 6)
    have b16153 := hb (x 14 5)
    have b16154 := hb (x 15 4)
    have b16155 := hb (x 16 11)
    have b16156 := hb (x 17 10)
    have b16157 := hb (x 18 9)
    have b16158 := hb (x 19 8)
    clear * - r16144 e16145 e16146 e16147 e16148 e16149 e16150 b16151 b16152 b16153 b16154 b16155 b16156 b16157 b16158 d16132
    omega
  have d16159 : (x 18 9).toNat = 0 := by
    have r16160 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16161 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e16162 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e16163 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e16164 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e16165 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e16166 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b16167 := hb (x 12 7)
    have b16168 := hb (x 13 6)
    have b16169 := hb (x 14 5)
    have b16170 := hb (x 15 4)
    have b16171 := hb (x 16 11)
    have b16172 := hb (x 17 10)
    have b16173 := hb (x 18 9)
    have b16174 := hb (x 19 8)
    clear * - r16160 e16161 e16162 e16163 e16164 e16165 e16166 b16167 b16168 b16169 b16170 b16171 b16172 b16173 b16174 d16143 d16132
    omega
  have d16175 : (x 17 10).toNat = 0 := by
    have r16176 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16177 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e16178 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e16179 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e16180 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e16181 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e16182 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b16183 := hb (x 12 7)
    have b16184 := hb (x 13 6)
    have b16185 := hb (x 14 5)
    have b16186 := hb (x 15 4)
    have b16187 := hb (x 16 11)
    have b16188 := hb (x 17 10)
    have b16189 := hb (x 18 9)
    have b16190 := hb (x 19 8)
    clear * - r16176 e16177 e16178 e16179 e16180 e16181 e16182 b16183 b16184 b16185 b16186 b16187 b16188 b16189 b16190 d16143 d16159 d16132
    omega
  have d16191 : (x 17 1 && x 17 10).toNat = 0 := by
    have r16192 := hand2 (x 17 1) (x 17 10)
    have b16193 := hb (x 17 10)
    have b16194 := hb (x 17 1 && x 17 10)
    clear * - r16192 b16193 b16194 d16175
    omega
  have d16195 : (x 16 11).toNat = 0 := by
    have r16196 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16197 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e16198 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e16199 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e16200 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e16201 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e16202 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b16203 := hb (x 12 7)
    have b16204 := hb (x 13 6)
    have b16205 := hb (x 14 5)
    have b16206 := hb (x 15 4)
    have b16207 := hb (x 16 11)
    have b16208 := hb (x 17 10)
    have b16209 := hb (x 18 9)
    have b16210 := hb (x 19 8)
    clear * - r16196 e16197 e16198 e16199 e16200 e16201 e16202 b16203 b16204 b16205 b16206 b16207 b16208 b16209 b16210 d16143 d16159 d16175 d16132
    omega
  have d16211 : (x 16 2 && x 16 11).toNat = 0 := by
    have r16212 := hand2 (x 16 2) (x 16 11)
    have b16213 := hb (x 16 11)
    have b16214 := hb (x 16 2 && x 16 11)
    clear * - r16212 b16213 b16214 d16195
    omega
  have d16215 : (x 15 3 && x 15 12).toNat = 1 := by
    have r16216 : 1 ≤ (x 18 9).toNat + (x 17 1 && x 17 10).toNat + (x 16 2 && x 16 11).toNat + (x 15 3 && x 15 12).toNat + (x 14 4 && x 14 13).toNat + (x 13 5 && x 13 14).toNat + (x 12 6).toNat := by have q := hcov9 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16217 := hb (x 12 6)
    have b16218 := hb (x 18 9)
    have b16219 := hb (x 17 1 && x 17 10)
    have b16220 := hb (x 16 2 && x 16 11)
    have b16221 := hb (x 15 3 && x 15 12)
    have b16222 := hb (x 14 4 && x 14 13)
    have b16223 := hb (x 13 5 && x 13 14)
    clear * - r16216 b16217 b16218 b16219 b16220 b16221 b16222 b16223 d16159 d16191 d16211 d15297 d15313 d15672
    omega
  have d16224 : (x 15 12).toNat = 1 := by
    have r16225 := hand2 (x 15 3) (x 15 12)
    have b16226 := hb (x 15 12)
    have b16227 := hb (x 15 3 && x 15 12)
    clear * - r16225 b16226 b16227 d16215
    omega
  have d16228 : (x 14 13).toNat = 0 := by
    have r16229 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16230 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e16231 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b16232 := hb (x 12 3)
    have b16233 := hb (x 13 2)
    have b16234 := hb (x 14 13)
    have b16235 := hb (x 15 12)
    clear * - r16229 e16230 e16231 b16232 b16233 b16234 b16235 d16224
    omega
  have d16236 : (x 14 5).toNat = 0 := by
    have r16237 : (x 14 5).toNat ≤ (x 14 13).toNat := himp _ _ (hp5 14)
    have b16238 := hb (x 14 5)
    have b16239 := hb (x 14 13)
    clear * - r16237 b16238 b16239 d16228
    omega
  have d16240 : (x 13 1 && x 13 14).toNat = 1 := by
    have r16241 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16242 := hb (x 12 2)
    have b16243 := hb (x 14 13)
    have b16244 := hb (x 13 1 && x 13 14)
    clear * - r16241 b16242 b16243 b16244 d16228 d15317
    omega
  have d16245 : (x 13 14).toNat = 1 := by
    have r16246 := hand2 (x 13 1) (x 13 14)
    have b16247 := hb (x 13 14)
    have b16248 := hb (x 13 1 && x 13 14)
    clear * - r16246 b16247 b16248 d16240
    omega
  have d16249 : (x 12 1).toNat = 0 := by
    have r16250 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16251 := hb (x 12 1)
    have b16252 := hb (x 13 14)
    clear * - r16250 b16251 b16252 d16245
    omega
  have d16253 : (x 12 1 && x 12 7).toNat = 0 := by
    have r16254 := hand1 (x 12 1) (x 12 7)
    have b16255 := hb (x 12 1)
    have b16256 := hb (x 12 1 && x 12 7)
    clear * - r16254 b16255 b16256 d16249
    omega
  have d16257 : (x 15 4).toNat = 0 := by
    have r16258 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16259 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e16260 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e16261 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e16262 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e16263 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e16264 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b16265 := hb (x 12 7)
    have b16266 := hb (x 13 6)
    have b16267 := hb (x 14 5)
    have b16268 := hb (x 15 4)
    have b16269 := hb (x 16 11)
    have b16270 := hb (x 17 10)
    have b16271 := hb (x 18 9)
    have b16272 := hb (x 19 8)
    clear * - r16258 e16259 e16260 e16261 e16262 e16263 e16264 b16265 b16266 b16267 b16268 b16269 b16270 b16271 b16272 d16143 d16159 d16175 d16195 d16236 d16132
    omega
  have d16273 : (x 13 6).toNat = 0 := by
    have r16274 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16275 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e16276 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e16277 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e16278 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e16279 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e16280 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b16281 := hb (x 12 7)
    have b16282 := hb (x 13 6)
    have b16283 := hb (x 14 5)
    have b16284 := hb (x 15 4)
    have b16285 := hb (x 16 11)
    have b16286 := hb (x 17 10)
    have b16287 := hb (x 18 9)
    have b16288 := hb (x 19 8)
    clear * - r16274 e16275 e16276 e16277 e16278 e16279 e16280 b16281 b16282 b16283 b16284 b16285 b16286 b16287 b16288 d16143 d16159 d16175 d16195 d16257 d16236 d16132
    omega
  have d16289 : (x 5 8 && x 5 14).toNat = 1 := by
    have r16290 : 1 ≤ (x 13 6).toNat + (x 12 1 && x 12 7).toNat + (x 11 2 && x 11 8).toNat + (x 10 3 && x 10 9).toNat + (x 9 4 && x 9 10).toNat + (x 8 5 && x 8 11).toNat + (x 7 6 && x 7 12).toNat + (x 6 7 && x 6 13).toNat + (x 5 8 && x 5 14).toNat + (x 4 9).toNat := by have q := hcov6 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16291 := hb (x 4 9)
    have b16292 := hb (x 13 6)
    have b16293 := hb (x 12 1 && x 12 7)
    have b16294 := hb (x 11 2 && x 11 8)
    have b16295 := hb (x 10 3 && x 10 9)
    have b16296 := hb (x 9 4 && x 9 10)
    have b16297 := hb (x 8 5 && x 8 11)
    have b16298 := hb (x 7 6 && x 7 12)
    have b16299 := hb (x 6 7 && x 6 13)
    have b16300 := hb (x 5 8 && x 5 14)
    clear * - r16290 b16291 b16292 b16293 b16294 b16295 b16296 b16297 b16298 b16299 b16300 d16273 d16253 d14846 d14870 d14898 d15019 d15878 d15043 d15068
    omega
  have d16301 : (x 5 8).toNat = 1 := by
    have r16302 := hand1 (x 5 8) (x 5 14)
    have b16303 := hb (x 5 8)
    have b16304 := hb (x 5 8 && x 5 14)
    clear * - r16302 b16303 b16304 d16289
    omega
  have d16305 : (x 3 10).toNat = 0 := by
    have r16306 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16307 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e16308 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e16309 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e16310 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e16311 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e16312 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b16313 := hb (x (-2) 7)
    have b16314 := hb (x (-1) 6)
    have b16315 := hb (x 0 5)
    have b16316 := hb (x 1 4)
    have b16317 := hb (x 2 11)
    have b16318 := hb (x 3 10)
    have b16319 := hb (x 4 9)
    have b16320 := hb (x 5 8)
    clear * - r16306 e16307 e16308 e16309 e16310 e16311 e16312 b16313 b16314 b16315 b16316 b16317 b16318 b16319 b16320 d16301 d15068 d14707 d14113 g5 d14270
    omega
  have d16321 : (x 3 4 && x 3 10).toNat = 0 := by
    have r16322 := hand2 (x 3 4) (x 3 10)
    have b16323 := hb (x 3 10)
    have b16324 := hb (x 3 4 && x 3 10)
    clear * - r16322 b16323 b16324 d16305
    omega
  have d16325 : (x (-2) 9).toNat = 1 := by
    have r16326 : 1 ≤ (x 7 6).toNat + (x 6 1 && x 6 7).toNat + (x 5 2 && x 5 8).toNat + (x 4 3 && x 4 9).toNat + (x 3 4 && x 3 10).toNat + (x 2 5 && x 2 11).toNat + (x 1 6 && x 1 12).toNat + (x 0 7 && x 0 13).toNat + (x (-1) 8 && x (-1) 14).toNat + (x (-2) 9).toNat := by have q := hcov6 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16327 := hb (x (-2) 9)
    have b16328 := hb (x 7 6)
    have b16329 := hb (x 6 1 && x 6 7)
    have b16330 := hb (x 5 2 && x 5 8)
    have b16331 := hb (x 4 3 && x 4 9)
    have b16332 := hb (x 3 4 && x 3 10)
    have b16333 := hb (x 2 5 && x 2 11)
    have b16334 := hb (x 1 6 && x 1 12)
    have b16335 := hb (x 0 7 && x 0 13)
    have b16336 := hb (x (-1) 8 && x (-1) 14)
    clear * - r16326 b16327 b16328 b16329 b16330 b16331 b16332 b16333 b16334 b16335 b16336 d15862 d14979 d15149 d15072 d16321 d14655 g17 d15490 d14266
    omega
  have d16337 : (x (-1) 8).toNat = 0 := by
    have r16338 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16339 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e16340 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e16341 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e16342 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e16343 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e16344 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b16345 := hb (x (-8) 7)
    have b16346 := hb (x (-7) 6)
    have b16347 := hb (x (-6) 5)
    have b16348 := hb (x (-5) 4)
    have b16349 := hb (x (-4) 11)
    have b16350 := hb (x (-3) 10)
    have b16351 := hb (x (-2) 9)
    have b16352 := hb (x (-1) 8)
    clear * - r16338 e16339 e16340 e16341 e16342 e16343 e16344 b16345 b16346 b16347 b16348 b16349 b16350 b16351 b16352 d16325 d14249 d14446
    omega
  have d16353 : (x (-5) 4).toNat = 0 := by
    have r16354 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16355 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e16356 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e16357 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e16358 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e16359 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e16360 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b16361 := hb (x (-8) 7)
    have b16362 := hb (x (-7) 6)
    have b16363 := hb (x (-6) 5)
    have b16364 := hb (x (-5) 4)
    have b16365 := hb (x (-4) 11)
    have b16366 := hb (x (-3) 10)
    have b16367 := hb (x (-2) 9)
    have b16368 := hb (x (-1) 8)
    clear * - r16354 e16355 e16356 e16357 e16358 e16359 e16360 b16361 b16362 b16363 b16364 b16365 b16366 b16367 b16368 d16337 d16325 d14249 d14446
    omega
  have d16369 : (x (-5) 4 && x (-5) 14).toNat = 0 := by
    have r16370 := hand1 (x (-5) 4) (x (-5) 14)
    have b16371 := hb (x (-5) 4)
    have b16372 := hb (x (-5) 4 && x (-5) 14)
    clear * - r16370 b16371 b16372 d16353
    omega
  have d16373 : (x (-6) 5).toNat = 1 := by
    have r16374 : 1 ≤ (x (-1) 10).toNat + (x (-2) 1 && x (-2) 11).toNat + (x (-3) 2 && x (-3) 12).toNat + (x (-4) 3 && x (-4) 13).toNat + (x (-5) 4 && x (-5) 14).toNat + (x (-6) 5).toNat := by have q := hcov10 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16375 := hb (x (-6) 5)
    have b16376 := hb (x (-1) 10)
    have b16377 := hb (x (-2) 1 && x (-2) 11)
    have b16378 := hb (x (-3) 2 && x (-3) 12)
    have b16379 := hb (x (-4) 3 && x (-4) 13)
    have b16380 := hb (x (-5) 4 && x (-5) 14)
    clear * - r16374 b16375 b16376 b16377 b16378 b16379 b16380 d14125 d14141 d14245 d14442 d16369
    omega
  have d16381 : (x (-6) 13).toNat = 1 := by
    have r16382 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
    have b16383 := hb (x (-6) 5)
    have b16384 := hb (x (-6) 13)
    clear * - r16382 b16383 b16384 d16373
    omega
  have d16385 : (x (-5) 12).toNat = 0 := by
    have r16386 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16387 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e16388 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have b16389 := hb (x (-8) 3)
    have b16390 := hb (x (-7) 2)
    have b16391 := hb (x (-6) 13)
    have b16392 := hb (x (-5) 12)
    clear * - r16386 e16387 e16388 b16389 b16390 b16391 b16392 d16381
    omega
  have d16393 : (x (-7) 2).toNat = 0 := by
    have r16394 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16395 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e16396 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have b16397 := hb (x (-8) 3)
    have b16398 := hb (x (-7) 2)
    have b16399 := hb (x (-6) 13)
    have b16400 := hb (x (-5) 12)
    clear * - r16394 e16395 e16396 b16397 b16398 b16399 b16400 d16385 d16381
    omega
  have d16401 : (x (-7) 2 && x (-7) 12).toNat = 0 := by
    have r16402 := hand1 (x (-7) 2) (x (-7) 12)
    have b16403 := hb (x (-7) 2)
    have b16404 := hb (x (-7) 2 && x (-7) 12)
    clear * - r16402 b16403 b16404 d16393
    omega
  have d16405 : (x (-8) 3).toNat = 0 := by
    have r16406 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16407 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e16408 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have b16409 := hb (x (-8) 3)
    have b16410 := hb (x (-7) 2)
    have b16411 := hb (x (-6) 13)
    have b16412 := hb (x (-5) 12)
    clear * - r16406 e16407 e16408 b16409 b16410 b16411 b16412 d16385 d16381 d16393
    omega
  have d16413 : (x (-8) 3 && x (-8) 13).toNat = 0 := by
    have r16414 := hand1 (x (-8) 3) (x (-8) 13)
    have b16415 := hb (x (-8) 3)
    have b16416 := hb (x (-8) 3 && x (-8) 13)
    clear * - r16414 b16415 b16416 d16405
    omega
  have d16417 : (x (-8) 11).toNat = 0 := by
    have r16418 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
    have b16419 := hb (x (-8) 3)
    have b16420 := hb (x (-8) 11)
    clear * - r16418 b16419 b16420 d16405
    omega
  have d16421 : (x (-9) 1 && x (-9) 12).toNat = 1 := by
    have r16422 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16423 := hb (x (-12) 4)
    have b16424 := hb (x (-8) 11)
    have b16425 := hb (x (-9) 1 && x (-9) 12)
    have b16426 := hb (x (-10) 2 && x (-10) 13)
    have b16427 := hb (x (-11) 3 && x (-11) 14)
    clear * - r16422 b16423 b16424 b16425 b16426 b16427 d16417 d14485 d14501 d15521
    omega
  have d16428 : (x (-9) 12).toNat = 1 := by
    have r16429 := hand2 (x (-9) 1) (x (-9) 12)
    have b16430 := hb (x (-9) 12)
    have b16431 := hb (x (-9) 1 && x (-9) 12)
    clear * - r16429 b16430 b16431 d16421
    omega
  have d16432 : (x (-10) 13).toNat = 0 := by
    have r16433 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e16434 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
    have e16435 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
    have b16436 := hb (x (-12) 3)
    have b16437 := hb (x (-11) 2)
    have b16438 := hb (x (-10) 13)
    have b16439 := hb (x (-9) 12)
    clear * - r16433 e16434 e16435 b16436 b16437 b16438 b16439 d16428
    omega
  have d16440 : (x (-10) 5).toNat = 0 := by
    have r16441 : (x (-10) 5).toNat ≤ (x (-10) 13).toNat := himp _ _ (hp5 (-10))
    have b16442 := hb (x (-10) 5)
    have b16443 := hb (x (-10) 13)
    clear * - r16441 b16442 b16443 d16432
    omega
  have d16444 : (x (-9) 4 && x (-9) 14).toNat = 1 := by
    have r16445 : 1 ≤ (x (-5) 10).toNat + (x (-6) 1 && x (-6) 11).toNat + (x (-7) 2 && x (-7) 12).toNat + (x (-8) 3 && x (-8) 13).toNat + (x (-9) 4 && x (-9) 14).toNat + (x (-10) 5).toNat := by have q := hcov10 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16446 := hb (x (-10) 5)
    have b16447 := hb (x (-5) 10)
    have b16448 := hb (x (-6) 1 && x (-6) 11)
    have b16449 := hb (x (-7) 2 && x (-7) 12)
    have b16450 := hb (x (-8) 3 && x (-8) 13)
    have b16451 := hb (x (-9) 4 && x (-9) 14)
    clear * - r16445 b16446 b16447 b16448 b16449 b16450 b16451 d14290 d14306 d16401 d16413 d16440
    omega
  have d16452 : (x (-9) 14).toNat = 1 := by
    have r16453 := hand2 (x (-9) 4) (x (-9) 14)
    have b16454 := hb (x (-9) 14)
    have b16455 := hb (x (-9) 4 && x (-9) 14)
    clear * - r16453 b16454 b16455 d16444
    omega
  have d16456 : (x (-10) 1).toNat = 0 := by
    have r16457 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16458 := hb (x (-10) 1)
    have b16459 := hb (x (-9) 14)
    clear * - r16457 b16458 b16459 d16452
    omega
  have d16460 : (x (-10) 1 && x (-10) 14).toNat = 0 := by
    have r16461 := hand1 (x (-10) 1) (x (-10) 14)
    have b16462 := hb (x (-10) 1)
    have b16463 := hb (x (-10) 1 && x (-10) 14)
    clear * - r16461 b16462 b16463 d16456
    omega
  have d16464 : (x (-11) 2).toNat = 1 := by
    have r16465 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b16466 := hb (x (-11) 2)
    have b16467 := hb (x (-9) 13)
    have b16468 := hb (x (-10) 1 && x (-10) 14)
    clear * - r16465 b16466 b16467 b16468 d14465 d16460
    omega
  have r16469 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e16470 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
  have e16471 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
  have b16472 := hb (x (-12) 3)
  have b16473 := hb (x (-11) 2)
  have b16474 := hb (x (-10) 13)
  have b16475 := hb (x (-9) 12)
  linarith only [r16469, e16470, e16471, b16472, b16473, b16474, b16475, d16428, d16432, d16464]

theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a00011 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 11).toNat = 0)
    (g1 : (x (-2) 2).toNat = 0)
    (g2 : (x (-2) 10).toNat = 0)
    (g3 : (x (-1) 13).toNat = 0)
    (g4 : (x 0 2).toNat = 1)
    (g5 : (x 0 5).toNat = 0)
    (g6 : (x 0 10).toNat = 0)
    (g7 : (x 0 11).toNat = 0)
    (g8 : (x 1 2).toNat = 0)
    (g9 : (x 1 6).toNat = 0)
    (g10 : (x 1 10).toNat = 0)
    (g11 : (x 3 9).toNat = 0)
    (g12 : (x 4 8).toNat = 0)
    (g13 : (x 0 4 && x 0 10).toNat = 0)
    (g14 : (x (-1) 5 && x (-1) 11).toNat = 0)
    (g15 : (x (-2) 6 && x (-2) 12).toNat = 0)
    (g16 : (x (-3) 7 && x (-3) 13).toNat = 0)
    (g17 : (x 1 6 && x 1 12).toNat = 0)
    (g18 : (x 4 8 && x 4 14).toNat = 0)
    (g19 : (x (-2) 2 && x (-2) 9).toNat = 0)
    (g20 : (x (-3) 3 && x (-3) 10).toNat = 0)
    (g21 : (x 1 3 && x 1 10).toNat = 0)
    (g22 : (x 0 4 && x 0 11).toNat = 0)
    (g23 : (x (-1) 5 && x (-1) 12).toNat = 0)
    (g24 : (x (-2) 6 && x (-2) 13).toNat = 0)
    (g25 : (x (-3) 7 && x (-3) 14).toNat = 0)
    (g26 : (x 2 1 && x 2 10).toNat = 0)
    (g27 : (x 1 2 && x 1 11).toNat = 0)
    (g28 : (x 0 3 && x 0 12).toNat = 0)
    (g29 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g30 : (x 0 5 && x 0 14).toNat = 0)
    (g31 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g32 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g33 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g34 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g35 : (x 1 2 && x 1 13).toNat = 0)
    (g36 : (x 0 3 && x 0 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a00011_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36
