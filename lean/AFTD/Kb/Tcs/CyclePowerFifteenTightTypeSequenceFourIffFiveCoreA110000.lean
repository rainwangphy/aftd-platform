import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a110000

Topic: combinatorics   Node: 8c36a6bc5a79

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_four_iff_five_core: under the layer-free tight-cover constraints for k = 15 and 38 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a10.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a10 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 6).toNat = 0)
    (g1 : (x (-3) 11).toNat = 0)
    (g2 : (x (-1) 13).toNat = 0)
    (g3 : (x 0 3).toNat = 0)
    (g4 : (x 0 5).toNat = 0)
    (g5 : (x 1 2).toNat = 0)
    (g6 : (x 1 10).toNat = 0)
    (g7 : (x 1 1 && x 1 10).toNat = 0)
    (g8 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g9 : (x (-2) 4 && x (-2) 13).toNat = 0)
    (g10 : (x (-3) 5 && x (-3) 14).toNat = 0)
    (g11 : (x 2 3 && x 2 12).toNat = 0)
    (g12 : (x 1 4 && x 1 13).toNat = 0)
    (g13 : (x 0 5 && x 0 14).toNat = 0)
    (g14 : (x (-1) 2 && x (-1) 12).toNat = 0)
    (g15 : (x (-2) 3 && x (-2) 13).toNat = 0)
    (g16 : (x 1 4 && x 1 14).toNat = 0)
    (g17 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g18 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g19 : (x (-3) 3 && x (-3) 14).toNat = 0)
    (g20 : (x 2 1 && x 2 12).toNat = 0)
    (g21 : (x 1 2 && x 1 13).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d26237 : (x 0 3 && x 0 14).toNat = 0 := by
    have r26238 := hand1 (x 0 3) (x 0 14)
    have b26239 := hb (x 0 3)
    have b26240 := hb (x 0 3 && x 0 14)
    clear * - r26238 b26239 b26240 g3
    omega
  have d26241 : (x 0 11).toNat = 0 := by
    have r26242 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
    have b26243 := hb (x 0 3)
    have b26244 := hb (x 0 11)
    clear * - r26242 b26243 b26244 g3
    omega
  have d26245 : (x 0 1 && x 0 11).toNat = 0 := by
    have r26246 := hand2 (x 0 1) (x 0 11)
    have b26247 := hb (x 0 11)
    have b26248 := hb (x 0 1 && x 0 11)
    clear * - r26246 b26247 b26248 d26241
    omega
  have d26249 : (x 0 2 && x 0 11).toNat = 0 := by
    have r26250 := hand2 (x 0 2) (x 0 11)
    have b26251 := hb (x 0 11)
    have b26252 := hb (x 0 2 && x 0 11)
    clear * - r26250 b26251 b26252 d26241
    omega
  have d26253 : (x (-4) 4).toNat = 1 := by
    have r26254 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26255 := hb (x (-4) 4)
    have b26256 := hb (x 0 11)
    have b26257 := hb (x (-1) 1 && x (-1) 12)
    have b26258 := hb (x (-2) 2 && x (-2) 13)
    have b26259 := hb (x (-3) 3 && x (-3) 14)
    clear * - r26254 b26255 b26256 b26257 b26258 b26259 d26241 g17 g18 g19
    omega
  have d26260 : (x (-4) 12).toNat = 1 := by
    have r26261 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have b26262 := hb (x (-4) 4)
    have b26263 := hb (x (-4) 12)
    clear * - r26261 b26262 b26263 d26253
    omega
  have d26264 : (x (-5) 13).toNat = 0 := by
    have r26265 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26266 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e26267 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b26268 := hb (x (-7) 3)
    have b26269 := hb (x (-6) 2)
    have b26270 := hb (x (-5) 13)
    have b26271 := hb (x (-4) 12)
    clear * - r26265 e26266 e26267 b26268 b26269 b26270 b26271 d26260
    omega
  have d26272 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
    have r26273 := hand2 (x (-5) 2) (x (-5) 13)
    have b26274 := hb (x (-5) 13)
    have b26275 := hb (x (-5) 2 && x (-5) 13)
    clear * - r26273 b26274 b26275 d26264
    omega
  have d26276 : (x (-6) 2).toNat = 0 := by
    have r26277 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26278 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e26279 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b26280 := hb (x (-7) 3)
    have b26281 := hb (x (-6) 2)
    have b26282 := hb (x (-5) 13)
    have b26283 := hb (x (-4) 12)
    clear * - r26277 e26278 e26279 b26280 b26281 b26282 b26283 d26260 d26264
    omega
  have d26284 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
    have r26285 := hand1 (x (-6) 2) (x (-6) 13)
    have b26286 := hb (x (-6) 2)
    have b26287 := hb (x (-6) 2 && x (-6) 13)
    clear * - r26285 b26286 b26287 d26276
    omega
  have d26288 : (x (-6) 2 && x (-6) 11).toNat = 0 := by
    have r26289 := hand1 (x (-6) 2) (x (-6) 11)
    have b26290 := hb (x (-6) 2)
    have b26291 := hb (x (-6) 2 && x (-6) 11)
    clear * - r26289 b26290 b26291 d26276
    omega
  have d26292 : (x (-7) 3).toNat = 0 := by
    have r26293 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26294 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e26295 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b26296 := hb (x (-7) 3)
    have b26297 := hb (x (-6) 2)
    have b26298 := hb (x (-5) 13)
    have b26299 := hb (x (-4) 12)
    clear * - r26293 e26294 e26295 b26296 b26297 b26298 b26299 d26260 d26264 d26276
    omega
  have d26300 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
    have r26301 := hand1 (x (-7) 3) (x (-7) 14)
    have b26302 := hb (x (-7) 3)
    have b26303 := hb (x (-7) 3 && x (-7) 14)
    clear * - r26301 b26302 b26303 d26292
    omega
  have d26304 : (x (-7) 3 && x (-7) 12).toNat = 0 := by
    have r26305 := hand1 (x (-7) 3) (x (-7) 12)
    have b26306 := hb (x (-7) 3)
    have b26307 := hb (x (-7) 3 && x (-7) 12)
    clear * - r26305 b26306 b26307 d26292
    omega
  have d26308 : (x (-7) 11).toNat = 0 := by
    have r26309 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have b26310 := hb (x (-7) 3)
    have b26311 := hb (x (-7) 11)
    clear * - r26309 b26310 b26311 d26292
    omega
  have d26312 : (x 2 9).toNat = 1 := by
    have r26313 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26314 := hb (x (-4) 6)
    have b26315 := hb (x 2 9)
    have b26316 := hb (x 1 1 && x 1 10)
    have b26317 := hb (x 0 2 && x 0 11)
    have b26318 := hb (x (-1) 3 && x (-1) 12)
    have b26319 := hb (x (-2) 4 && x (-2) 13)
    have b26320 := hb (x (-3) 5 && x (-3) 14)
    clear * - r26313 b26314 b26315 b26316 b26317 b26318 b26319 b26320 g7 d26249 g8 g9 g10 g0
    omega
  have d26321 : (x 2 1).toNat = 1 := by
    have r26322 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
    have b26323 := hb (x 2 1)
    have b26324 := hb (x 2 9)
    clear * - r26322 b26323 b26324 d26312
    omega
  have d26325 : (x 3 14).toNat = 0 := by
    have r26326 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26327 := hb (x 2 1)
    have b26328 := hb (x 3 14)
    clear * - r26326 b26327 b26328 d26321
    omega
  have d26329 : (x 3 2).toNat = 0 := by
    have r26330 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b26331 := hb (x 3 2)
    have b26332 := hb (x 3 14)
    clear * - r26330 b26331 b26332 d26325
    omega
  have d26333 : (x 3 2 && x 3 12).toNat = 0 := by
    have r26334 := hand1 (x 3 2) (x 3 12)
    have b26335 := hb (x 3 2)
    have b26336 := hb (x 3 2 && x 3 12)
    clear * - r26334 b26335 b26336 d26329
    omega
  have d26337 : (x 3 2 && x 3 11).toNat = 0 := by
    have r26338 := hand1 (x 3 2) (x 3 11)
    have b26339 := hb (x 3 2)
    have b26340 := hb (x 3 2 && x 3 11)
    clear * - r26338 b26339 b26340 d26329
    omega
  have d26341 : (x 3 8).toNat = 0 := by
    have r26342 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26343 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e26344 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e26345 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e26346 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e26347 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e26348 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b26349 := hb (x (-4) 7)
    have b26350 := hb (x (-3) 6)
    have b26351 := hb (x (-2) 5)
    have b26352 := hb (x (-1) 4)
    have b26353 := hb (x 0 11)
    have b26354 := hb (x 1 10)
    have b26355 := hb (x 2 9)
    have b26356 := hb (x 3 8)
    clear * - r26342 e26343 e26344 e26345 e26346 e26347 e26348 b26349 b26350 b26351 b26352 b26353 b26354 b26355 b26356 d26312 g6 d26241
    omega
  have d26357 : (x (-1) 4).toNat = 0 := by
    have r26358 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26359 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e26360 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e26361 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e26362 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e26363 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e26364 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b26365 := hb (x (-4) 7)
    have b26366 := hb (x (-3) 6)
    have b26367 := hb (x (-2) 5)
    have b26368 := hb (x (-1) 4)
    have b26369 := hb (x 0 11)
    have b26370 := hb (x 1 10)
    have b26371 := hb (x 2 9)
    have b26372 := hb (x 3 8)
    clear * - r26358 e26359 e26360 e26361 e26362 e26363 e26364 b26365 b26366 b26367 b26368 b26369 b26370 b26371 b26372 d26341 d26312 g6 d26241
    omega
  have d26373 : (x 3 11).toNat = 1 := by
    have r26374 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26375 := hb (x (-1) 4)
    have b26376 := hb (x 3 11)
    have b26377 := hb (x 2 1 && x 2 12)
    have b26378 := hb (x 1 2 && x 1 13)
    have b26379 := hb (x 0 3 && x 0 14)
    clear * - r26374 b26375 b26376 b26377 b26378 b26379 g20 g21 d26237 d26357
    omega
  have d26380 : (x 3 3).toNat = 1 := by
    have r26381 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b26382 := hb (x 3 3)
    have b26383 := hb (x 3 11)
    clear * - r26381 b26382 b26383 d26373
    omega
  have d26384 : (x 6 12).toNat = 0 := by
    have r26385 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26386 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e26387 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b26388 := hb (x 3 3)
    have b26389 := hb (x 4 2)
    have b26390 := hb (x 5 13)
    have b26391 := hb (x 6 12)
    clear * - r26385 e26386 e26387 b26388 b26389 b26390 b26391 d26380
    omega
  have d26392 : (x 6 1 && x 6 12).toNat = 0 := by
    have r26393 := hand2 (x 6 1) (x 6 12)
    have b26394 := hb (x 6 12)
    have b26395 := hb (x 6 1 && x 6 12)
    clear * - r26393 b26394 b26395 d26384
    omega
  have d26396 : (x 5 13).toNat = 0 := by
    have r26397 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26398 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e26399 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b26400 := hb (x 3 3)
    have b26401 := hb (x 4 2)
    have b26402 := hb (x 5 13)
    have b26403 := hb (x 6 12)
    clear * - r26397 e26398 e26399 b26400 b26401 b26402 b26403 d26384 d26380
    omega
  have d26404 : (x 5 2 && x 5 13).toNat = 0 := by
    have r26405 := hand2 (x 5 2) (x 5 13)
    have b26406 := hb (x 5 13)
    have b26407 := hb (x 5 2 && x 5 13)
    clear * - r26405 b26406 b26407 d26396
    omega
  have d26408 : (x 4 1 && x 4 14).toNat = 1 := by
    have r26409 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26410 := hb (x 3 2)
    have b26411 := hb (x 5 13)
    have b26412 := hb (x 4 1 && x 4 14)
    clear * - r26409 b26410 b26411 b26412 d26396 d26329
    omega
  have d26413 : (x 4 1).toNat = 1 := by
    have r26414 := hand1 (x 4 1) (x 4 14)
    have b26415 := hb (x 4 1)
    have b26416 := hb (x 4 1 && x 4 14)
    clear * - r26414 b26415 b26416 d26408
    omega
  have d26417 : (x 5 14).toNat = 0 := by
    have r26418 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26419 := hb (x 4 1)
    have b26420 := hb (x 5 14)
    clear * - r26418 b26419 b26420 d26413
    omega
  have d26421 : (x 5 1 && x 5 14).toNat = 0 := by
    have r26422 := hand2 (x 5 1) (x 5 14)
    have b26423 := hb (x 5 14)
    have b26424 := hb (x 5 1 && x 5 14)
    clear * - r26422 b26423 b26424 d26417
    omega
  have d26425 : (x 5 2).toNat = 0 := by
    have r26426 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b26427 := hb (x 5 2)
    have b26428 := hb (x 5 14)
    clear * - r26426 b26427 b26428 d26417
    omega
  have d26429 : (x 5 10).toNat = 0 := by
    have r26430 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
    have b26431 := hb (x 5 2)
    have b26432 := hb (x 5 10)
    clear * - r26430 b26431 b26432 d26425
    omega
  have d26433 : (x 4 2).toNat = 0 := by
    have r26434 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26435 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e26436 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b26437 := hb (x 3 3)
    have b26438 := hb (x 4 2)
    have b26439 := hb (x 5 13)
    have b26440 := hb (x 6 12)
    clear * - r26434 e26435 e26436 b26437 b26438 b26439 b26440 d26384 d26396 d26380
    omega
  have d26441 : (x 4 10).toNat = 0 := by
    have r26442 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
    have b26443 := hb (x 4 2)
    have b26444 := hb (x 4 10)
    clear * - r26442 b26443 b26444 d26433
    omega
  have d26445 : (x 4 1 && x 4 10).toNat = 0 := by
    have r26446 := hand2 (x 4 1) (x 4 10)
    have b26447 := hb (x 4 10)
    have b26448 := hb (x 4 1 && x 4 10)
    clear * - r26446 b26447 b26448 d26441
    omega
  have d26449 : (x 6 13).toNat = 1 := by
    have r26450 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26451 := hb (x 4 2)
    have b26452 := hb (x 6 13)
    have b26453 := hb (x 5 1 && x 5 14)
    clear * - r26450 b26451 b26452 b26453 d26421 d26433
    omega
  have d26454 : (x 6 1).toNat = 1 := by
    have r26455 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b26456 := hb (x 6 1)
    have b26457 := hb (x 6 13)
    clear * - r26455 b26456 b26457 d26449
    omega
  have d26458 : (x 7 14).toNat = 0 := by
    have r26459 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26460 := hb (x 6 1)
    have b26461 := hb (x 7 14)
    clear * - r26459 b26460 b26461 d26454
    omega
  have d26462 : (x 7 2).toNat = 0 := by
    have r26463 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b26464 := hb (x 7 2)
    have b26465 := hb (x 7 14)
    clear * - r26463 b26464 b26465 d26458
    omega
  have d26466 : (x 7 12).toNat = 0 := by
    have r26467 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26468 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e26469 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b26470 := hb (x 4 3)
    have b26471 := hb (x 5 2)
    have b26472 := hb (x 6 13)
    have b26473 := hb (x 7 12)
    clear * - r26467 e26468 e26469 b26470 b26471 b26472 b26473 d26449 d26425
    omega
  have d26474 : (x 4 3).toNat = 0 := by
    have r26475 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26476 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e26477 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b26478 := hb (x 4 3)
    have b26479 := hb (x 5 2)
    have b26480 := hb (x 6 13)
    have b26481 := hb (x 7 12)
    clear * - r26475 e26476 e26477 b26478 b26479 b26480 b26481 d26466 d26449 d26425
    omega
  have d26482 : (x 4 3 && x 4 14).toNat = 0 := by
    have r26483 := hand1 (x 4 3) (x 4 14)
    have b26484 := hb (x 4 3)
    have b26485 := hb (x 4 3 && x 4 14)
    clear * - r26483 b26484 b26485 d26474
    omega
  have d26486 : (x 4 11).toNat = 0 := by
    have r26487 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have b26488 := hb (x 4 3)
    have b26489 := hb (x 4 11)
    clear * - r26487 b26488 b26489 d26474
    omega
  have d26490 : (x 4 1 && x 4 11).toNat = 0 := by
    have r26491 := hand2 (x 4 1) (x 4 11)
    have b26492 := hb (x 4 11)
    have b26493 := hb (x 4 1 && x 4 11)
    clear * - r26491 b26492 b26493 d26486
    omega
  have d26494 : (x 2 3 && x 2 13).toNat = 1 := by
    have r26495 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26496 := hb (x 0 5)
    have b26497 := hb (x 5 10)
    have b26498 := hb (x 4 1 && x 4 11)
    have b26499 := hb (x 3 2 && x 3 12)
    have b26500 := hb (x 2 3 && x 2 13)
    have b26501 := hb (x 1 4 && x 1 14)
    clear * - r26495 b26496 b26497 b26498 b26499 b26500 b26501 d26429 d26490 d26333 g16 g4
    omega
  have d26502 : (x 2 13).toNat = 1 := by
    have r26503 := hand2 (x 2 3) (x 2 13)
    have b26504 := hb (x 2 13)
    have b26505 := hb (x 2 3 && x 2 13)
    clear * - r26503 b26504 b26505 d26494
    omega
  have d26506 : (x 3 12).toNat = 0 := by
    have r26507 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26508 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e26509 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b26510 := hb (x 0 3)
    have b26511 := hb (x 1 2)
    have b26512 := hb (x 2 13)
    have b26513 := hb (x 3 12)
    clear * - r26507 e26508 e26509 b26510 b26511 b26512 b26513 d26502 g5 g3
    omega
  have d26514 : (x 3 4).toNat = 0 := by
    have r26515 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
    have b26516 := hb (x 3 4)
    have b26517 := hb (x 3 12)
    clear * - r26515 b26516 b26517 d26506
    omega
  have d26518 : (x 7 11).toNat = 1 := by
    have r26519 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26520 := hb (x 3 4)
    have b26521 := hb (x 7 11)
    have b26522 := hb (x 6 1 && x 6 12)
    have b26523 := hb (x 5 2 && x 5 13)
    have b26524 := hb (x 4 3 && x 4 14)
    clear * - r26519 b26520 b26521 b26522 b26523 b26524 d26392 d26404 d26482 d26514
    omega
  have d26525 : (x 7 3).toNat = 1 := by
    have r26526 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b26527 := hb (x 7 3)
    have b26528 := hb (x 7 11)
    clear * - r26526 b26527 b26528 d26518
    omega
  have d26529 : (x 10 12).toNat = 0 := by
    have r26530 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26531 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e26532 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b26533 := hb (x 7 3)
    have b26534 := hb (x 8 2)
    have b26535 := hb (x 9 13)
    have b26536 := hb (x 10 12)
    clear * - r26530 e26531 e26532 b26533 b26534 b26535 b26536 d26525
    omega
  have d26537 : (x 9 13).toNat = 0 := by
    have r26538 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26539 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e26540 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b26541 := hb (x 7 3)
    have b26542 := hb (x 8 2)
    have b26543 := hb (x 9 13)
    have b26544 := hb (x 10 12)
    clear * - r26538 e26539 e26540 b26541 b26542 b26543 b26544 d26529 d26525
    omega
  have d26545 : (x 8 1 && x 8 14).toNat = 1 := by
    have r26546 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26547 := hb (x 7 2)
    have b26548 := hb (x 9 13)
    have b26549 := hb (x 8 1 && x 8 14)
    clear * - r26546 b26547 b26548 b26549 d26537 d26462
    omega
  have d26550 : (x 8 14).toNat = 1 := by
    have r26551 := hand2 (x 8 1) (x 8 14)
    have b26552 := hb (x 8 14)
    have b26553 := hb (x 8 1 && x 8 14)
    clear * - r26551 b26552 b26553 d26545
    omega
  have d26554 : (x 7 1).toNat = 0 := by
    have r26555 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26556 := hb (x 7 1)
    have b26557 := hb (x 8 14)
    clear * - r26555 b26556 b26557 d26550
    omega
  have d26558 : (x 7 13).toNat = 0 := by
    have r26559 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b26560 := hb (x 7 1)
    have b26561 := hb (x 7 13)
    clear * - r26559 b26560 b26561 d26554
    omega
  have d26562 : (x 6 1 && x 6 14).toNat = 1 := by
    have r26563 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26564 := hb (x 5 2)
    have b26565 := hb (x 7 13)
    have b26566 := hb (x 6 1 && x 6 14)
    clear * - r26563 b26564 b26565 b26566 d26558 d26425
    omega
  have d26567 : (x 6 14).toNat = 1 := by
    have r26568 := hand2 (x 6 1) (x 6 14)
    have b26569 := hb (x 6 14)
    have b26570 := hb (x 6 1 && x 6 14)
    clear * - r26568 b26569 b26570 d26562
    omega
  have d26571 : (x 5 1).toNat = 0 := by
    have r26572 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26573 := hb (x 5 1)
    have b26574 := hb (x 6 14)
    clear * - r26572 b26573 b26574 d26567
    omega
  have d26575 : (x 5 9).toNat = 0 := by
    have r26576 : (x 5 9).toNat ≤ (x 5 1).toNat := himp _ _ (hp9 5)
    have b26577 := hb (x 5 1)
    have b26578 := hb (x 5 9)
    clear * - r26576 b26577 b26578 d26571
    omega
  have d26579 : (x (-1) 6).toNat = 1 := by
    have r26580 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26581 := hb (x (-1) 6)
    have b26582 := hb (x 5 9)
    have b26583 := hb (x 4 1 && x 4 10)
    have b26584 := hb (x 3 2 && x 3 11)
    have b26585 := hb (x 2 3 && x 2 12)
    have b26586 := hb (x 1 4 && x 1 13)
    have b26587 := hb (x 0 5 && x 0 14)
    clear * - r26580 b26581 b26582 b26583 b26584 b26585 b26586 b26587 d26575 d26445 d26337 g11 g12 g13
    omega
  have d26588 : (x (-1) 14).toNat = 1 := by
    have r26589 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
    have b26590 := hb (x (-1) 6)
    have b26591 := hb (x (-1) 14)
    clear * - r26589 b26590 b26591 d26579
    omega
  have d26592 : (x (-2) 1).toNat = 0 := by
    have r26593 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26594 := hb (x (-2) 1)
    have b26595 := hb (x (-1) 14)
    clear * - r26593 b26594 b26595 d26588
    omega
  have d26596 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r26597 := hand1 (x (-2) 1) (x (-2) 14)
    have b26598 := hb (x (-2) 1)
    have b26599 := hb (x (-2) 1 && x (-2) 14)
    clear * - r26597 b26598 b26599 d26592
    omega
  have d26600 : (x (-3) 2).toNat = 1 := by
    have r26601 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26602 := hb (x (-3) 2)
    have b26603 := hb (x (-1) 13)
    have b26604 := hb (x (-2) 1 && x (-2) 14)
    clear * - r26601 b26602 b26603 b26604 g2 d26596
    omega
  have d26605 : (x (-3) 14).toNat = 1 := by
    have r26606 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b26607 := hb (x (-3) 2)
    have b26608 := hb (x (-3) 14)
    clear * - r26606 b26607 b26608 d26600
    omega
  have d26609 : (x (-4) 1).toNat = 0 := by
    have r26610 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26611 := hb (x (-4) 1)
    have b26612 := hb (x (-3) 14)
    clear * - r26610 b26611 b26612 d26605
    omega
  have d26613 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
    have r26614 := hand1 (x (-4) 1) (x (-4) 12)
    have b26615 := hb (x (-4) 1)
    have b26616 := hb (x (-4) 1 && x (-4) 12)
    clear * - r26614 b26615 b26616 d26609
    omega
  have d26617 : (x (-4) 13).toNat = 0 := by
    have r26618 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b26619 := hb (x (-4) 1)
    have b26620 := hb (x (-4) 13)
    clear * - r26618 b26619 b26620 d26609
    omega
  have d26621 : (x (-4) 5).toNat = 0 := by
    have r26622 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
    have b26623 := hb (x (-4) 5)
    have b26624 := hb (x (-4) 13)
    clear * - r26622 b26623 b26624 d26617
    omega
  have d26625 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
    have r26626 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26627 := hb (x (-4) 5)
    have b26628 := hb (x 1 10)
    have b26629 := hb (x 0 1 && x 0 11)
    have b26630 := hb (x (-1) 2 && x (-1) 12)
    have b26631 := hb (x (-2) 3 && x (-2) 13)
    have b26632 := hb (x (-3) 4 && x (-3) 14)
    clear * - r26626 b26627 b26628 b26629 b26630 b26631 b26632 g6 d26245 g14 g15 d26621
    omega
  have d26633 : (x (-3) 4).toNat = 1 := by
    have r26634 := hand1 (x (-3) 4) (x (-3) 14)
    have b26635 := hb (x (-3) 4)
    have b26636 := hb (x (-3) 4 && x (-3) 14)
    clear * - r26634 b26635 b26636 d26625
    omega
  have d26637 : (x (-3) 12).toNat = 1 := by
    have r26638 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
    have b26639 := hb (x (-3) 4)
    have b26640 := hb (x (-3) 12)
    clear * - r26638 b26639 b26640 d26633
    omega
  have d26641 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
    have r26642 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26643 := hb (x (-6) 2)
    have b26644 := hb (x (-4) 13)
    have b26645 := hb (x (-5) 1 && x (-5) 14)
    clear * - r26642 b26643 b26644 b26645 d26617 d26276
    omega
  have d26646 : (x (-5) 14).toNat = 1 := by
    have r26647 := hand2 (x (-5) 1) (x (-5) 14)
    have b26648 := hb (x (-5) 14)
    have b26649 := hb (x (-5) 1 && x (-5) 14)
    clear * - r26647 b26648 b26649 d26641
    omega
  have d26650 : (x (-6) 1).toNat = 0 := by
    have r26651 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26652 := hb (x (-6) 1)
    have b26653 := hb (x (-5) 14)
    clear * - r26651 b26652 b26653 d26646
    omega
  have d26654 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
    have r26655 := hand1 (x (-6) 1) (x (-6) 14)
    have b26656 := hb (x (-6) 1)
    have b26657 := hb (x (-6) 1 && x (-6) 14)
    clear * - r26655 b26656 b26657 d26650
    omega
  have d26658 : (x (-7) 2).toNat = 1 := by
    have r26659 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26660 := hb (x (-7) 2)
    have b26661 := hb (x (-5) 13)
    have b26662 := hb (x (-6) 1 && x (-6) 14)
    clear * - r26659 b26660 b26661 b26662 d26264 d26654
    omega
  have d26663 : (x (-7) 14).toNat = 1 := by
    have r26664 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
    have b26665 := hb (x (-7) 2)
    have b26666 := hb (x (-7) 14)
    clear * - r26664 b26665 b26666 d26658
    omega
  have d26667 : (x (-8) 1).toNat = 0 := by
    have r26668 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26669 := hb (x (-8) 1)
    have b26670 := hb (x (-7) 14)
    clear * - r26668 b26669 b26670 d26663
    omega
  have d26671 : (x (-8) 1 && x (-8) 14).toNat = 0 := by
    have r26672 := hand1 (x (-8) 1) (x (-8) 14)
    have b26673 := hb (x (-8) 1)
    have b26674 := hb (x (-8) 1 && x (-8) 14)
    clear * - r26672 b26673 b26674 d26667
    omega
  have d26675 : (x (-8) 1 && x (-8) 12).toNat = 0 := by
    have r26676 := hand1 (x (-8) 1) (x (-8) 12)
    have b26677 := hb (x (-8) 1)
    have b26678 := hb (x (-8) 1 && x (-8) 12)
    clear * - r26676 b26677 b26678 d26667
    omega
  have d26679 : (x (-8) 13).toNat = 0 := by
    have r26680 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
    have b26681 := hb (x (-8) 1)
    have b26682 := hb (x (-8) 13)
    clear * - r26680 b26681 b26682 d26667
    omega
  have d26683 : (x (-8) 4 && x (-8) 13).toNat = 0 := by
    have r26684 := hand2 (x (-8) 4) (x (-8) 13)
    have b26685 := hb (x (-8) 13)
    have b26686 := hb (x (-8) 4 && x (-8) 13)
    clear * - r26684 b26685 b26686 d26679
    omega
  have d26687 : (x (-5) 12).toNat = 0 := by
    have r26688 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26689 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e26690 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have b26691 := hb (x (-8) 3)
    have b26692 := hb (x (-7) 2)
    have b26693 := hb (x (-6) 13)
    have b26694 := hb (x (-5) 12)
    clear * - r26688 e26689 e26690 b26691 b26692 b26693 b26694 d26658
    omega
  have d26695 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
    have r26696 := hand2 (x (-5) 1) (x (-5) 12)
    have b26697 := hb (x (-5) 12)
    have b26698 := hb (x (-5) 1 && x (-5) 12)
    clear * - r26696 b26697 b26698 d26687
    omega
  have d26699 : (x (-5) 2).toNat = 0 := by
    have r26700 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26701 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e26702 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b26703 := hb (x (-6) 3)
    have b26704 := hb (x (-5) 2)
    have b26705 := hb (x (-4) 13)
    have b26706 := hb (x (-3) 12)
    clear * - r26700 e26701 e26702 b26703 b26704 b26705 b26706 d26637 d26617
    omega
  have d26707 : (x (-5) 10).toNat = 0 := by
    have r26708 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
    have b26709 := hb (x (-5) 2)
    have b26710 := hb (x (-5) 10)
    clear * - r26708 b26709 b26710 d26699
    omega
  have d26711 : (x (-5) 1 && x (-5) 10).toNat = 0 := by
    have r26712 := hand2 (x (-5) 1) (x (-5) 10)
    have b26713 := hb (x (-5) 10)
    have b26714 := hb (x (-5) 1 && x (-5) 10)
    clear * - r26712 b26713 b26714 d26707
    omega
  have d26715 : (x (-6) 3).toNat = 0 := by
    have r26716 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26717 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e26718 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b26719 := hb (x (-6) 3)
    have b26720 := hb (x (-5) 2)
    have b26721 := hb (x (-4) 13)
    have b26722 := hb (x (-3) 12)
    clear * - r26716 e26717 e26718 b26719 b26720 b26721 b26722 d26637 d26617 d26699
    omega
  have d26723 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
    have r26724 := hand1 (x (-6) 3) (x (-6) 14)
    have b26725 := hb (x (-6) 3)
    have b26726 := hb (x (-6) 3 && x (-6) 14)
    clear * - r26724 b26725 b26726 d26715
    omega
  have d26727 : (x (-7) 4).toNat = 1 := by
    have r26728 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26729 := hb (x (-7) 4)
    have b26730 := hb (x (-3) 11)
    have b26731 := hb (x (-4) 1 && x (-4) 12)
    have b26732 := hb (x (-5) 2 && x (-5) 13)
    have b26733 := hb (x (-6) 3 && x (-6) 14)
    clear * - r26728 b26729 b26730 b26731 b26732 b26733 g1 d26613 d26272 d26723
    omega
  have d26734 : (x (-7) 12).toNat = 1 := by
    have r26735 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
    have b26736 := hb (x (-7) 4)
    have b26737 := hb (x (-7) 12)
    clear * - r26735 b26736 b26737 d26727
    omega
  have d26738 : (x (-9) 2).toNat = 0 := by
    have r26739 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26740 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
    have e26741 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
    have b26742 := hb (x (-10) 3)
    have b26743 := hb (x (-9) 2)
    have b26744 := hb (x (-8) 13)
    have b26745 := hb (x (-7) 12)
    clear * - r26739 e26740 e26741 b26742 b26743 b26744 b26745 d26734 d26679
    omega
  have d26746 : (x (-9) 2 && x (-9) 13).toNat = 0 := by
    have r26747 := hand1 (x (-9) 2) (x (-9) 13)
    have b26748 := hb (x (-9) 2)
    have b26749 := hb (x (-9) 2 && x (-9) 13)
    clear * - r26747 b26748 b26749 d26738
    omega
  have d26750 : (x (-7) 13).toNat = 1 := by
    have r26751 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26752 := hb (x (-9) 2)
    have b26753 := hb (x (-7) 13)
    have b26754 := hb (x (-8) 1 && x (-8) 14)
    clear * - r26751 b26752 b26753 b26754 d26671 d26738
    omega
  have d26755 : (x (-6) 12).toNat = 0 := by
    have r26756 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26757 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
    have e26758 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
    have b26759 := hb (x (-9) 3)
    have b26760 := hb (x (-8) 2)
    have b26761 := hb (x (-7) 13)
    have b26762 := hb (x (-6) 12)
    clear * - r26756 e26757 e26758 b26759 b26760 b26761 b26762 d26750
    omega
  have d26763 : (x (-8) 2).toNat = 0 := by
    have r26764 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26765 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
    have e26766 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
    have b26767 := hb (x (-9) 3)
    have b26768 := hb (x (-8) 2)
    have b26769 := hb (x (-7) 13)
    have b26770 := hb (x (-6) 12)
    clear * - r26764 e26765 e26766 b26767 b26768 b26769 b26770 d26755 d26750
    omega
  have d26771 : (x (-8) 10).toNat = 0 := by
    have r26772 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
    have b26773 := hb (x (-8) 2)
    have b26774 := hb (x (-8) 10)
    clear * - r26772 b26773 b26774 d26763
    omega
  have d26775 : (x (-9) 3).toNat = 0 := by
    have r26776 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26777 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
    have e26778 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
    have b26779 := hb (x (-9) 3)
    have b26780 := hb (x (-8) 2)
    have b26781 := hb (x (-7) 13)
    have b26782 := hb (x (-6) 12)
    clear * - r26776 e26777 e26778 b26779 b26780 b26781 b26782 d26755 d26750 d26763
    omega
  have d26783 : (x (-9) 11).toNat = 0 := by
    have r26784 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
    have b26785 := hb (x (-9) 3)
    have b26786 := hb (x (-9) 11)
    clear * - r26784 b26785 b26786 d26775
    omega
  have d26787 : (x (-9) 1 && x (-9) 11).toNat = 0 := by
    have r26788 := hand2 (x (-9) 1) (x (-9) 11)
    have b26789 := hb (x (-9) 11)
    have b26790 := hb (x (-9) 1 && x (-9) 11)
    clear * - r26788 b26789 b26790 d26783
    omega
  have d26791 : (x (-10) 3).toNat = 0 := by
    have r26792 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26793 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
    have e26794 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
    have b26795 := hb (x (-10) 3)
    have b26796 := hb (x (-9) 2)
    have b26797 := hb (x (-8) 13)
    have b26798 := hb (x (-7) 12)
    clear * - r26792 e26793 e26794 b26795 b26796 b26797 b26798 d26734 d26679 d26738
    omega
  have d26799 : (x (-10) 3 && x (-10) 14).toNat = 0 := by
    have r26800 := hand1 (x (-10) 3) (x (-10) 14)
    have b26801 := hb (x (-10) 3)
    have b26802 := hb (x (-10) 3 && x (-10) 14)
    clear * - r26800 b26801 b26802 d26791
    omega
  have d26803 : (x (-11) 4).toNat = 1 := by
    have r26804 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26805 := hb (x (-11) 4)
    have b26806 := hb (x (-7) 11)
    have b26807 := hb (x (-8) 1 && x (-8) 12)
    have b26808 := hb (x (-9) 2 && x (-9) 13)
    have b26809 := hb (x (-10) 3 && x (-10) 14)
    clear * - r26804 b26805 b26806 b26807 b26808 b26809 d26308 d26675 d26746 d26799
    omega
  have d26810 : (x (-11) 12).toNat = 1 := by
    have r26811 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
    have b26812 := hb (x (-11) 4)
    have b26813 := hb (x (-11) 12)
    clear * - r26811 b26812 b26813 d26803
    omega
  have d26814 : (x (-12) 13).toNat = 0 := by
    have r26815 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26816 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
    have e26817 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
    have b26818 := hb (x (-14) 3)
    have b26819 := hb (x (-13) 2)
    have b26820 := hb (x (-12) 13)
    have b26821 := hb (x (-11) 12)
    clear * - r26815 e26816 e26817 b26818 b26819 b26820 b26821 d26810
    omega
  have d26822 : (x (-13) 2).toNat = 0 := by
    have r26823 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26824 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
    have e26825 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
    have b26826 := hb (x (-14) 3)
    have b26827 := hb (x (-13) 2)
    have b26828 := hb (x (-12) 13)
    have b26829 := hb (x (-11) 12)
    clear * - r26823 e26824 e26825 b26826 b26827 b26828 b26829 d26810 d26814
    omega
  have d26830 : (x (-4) 9).toNat = 0 := by
    have r26831 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
    have b26832 := hb (x (-4) 1)
    have b26833 := hb (x (-4) 9)
    clear * - r26831 b26832 b26833 d26609
    omega
  have d26834 : (x (-1) 12).toNat = 0 := by
    have r26835 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26836 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e26837 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b26838 := hb (x (-4) 3)
    have b26839 := hb (x (-3) 2)
    have b26840 := hb (x (-2) 13)
    have b26841 := hb (x (-1) 12)
    clear * - r26835 e26836 e26837 b26838 b26839 b26840 b26841 d26600
    omega
  have d26842 : (x (-2) 13).toNat = 0 := by
    have r26843 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26844 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e26845 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b26846 := hb (x (-4) 3)
    have b26847 := hb (x (-3) 2)
    have b26848 := hb (x (-2) 13)
    have b26849 := hb (x (-1) 12)
    clear * - r26843 e26844 e26845 b26846 b26847 b26848 b26849 d26834 d26600
    omega
  have d26850 : (x (-4) 3).toNat = 0 := by
    have r26851 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26852 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e26853 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b26854 := hb (x (-4) 3)
    have b26855 := hb (x (-3) 2)
    have b26856 := hb (x (-2) 13)
    have b26857 := hb (x (-1) 12)
    clear * - r26851 e26852 e26853 b26854 b26855 b26856 b26857 d26834 d26842 d26600
    omega
  have d26858 : (x (-4) 11).toNat = 0 := by
    have r26859 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
    have b26860 := hb (x (-4) 3)
    have b26861 := hb (x (-4) 11)
    clear * - r26859 b26860 b26861 d26850
    omega
  have d26862 : (x (-8) 4).toNat = 1 := by
    have r26863 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26864 := hb (x (-8) 4)
    have b26865 := hb (x (-4) 11)
    have b26866 := hb (x (-5) 1 && x (-5) 12)
    have b26867 := hb (x (-6) 2 && x (-6) 13)
    have b26868 := hb (x (-7) 3 && x (-7) 14)
    clear * - r26863 b26864 b26865 b26866 b26867 b26868 d26858 d26695 d26284 d26300
    omega
  have d26869 : (x (-8) 12).toNat = 1 := by
    have r26870 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
    have b26871 := hb (x (-8) 4)
    have b26872 := hb (x (-8) 12)
    clear * - r26870 b26871 b26872 d26862
    omega
  have d26873 : (x (-9) 13).toNat = 0 := by
    have r26874 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26875 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
    have e26876 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
    have b26877 := hb (x (-11) 3)
    have b26878 := hb (x (-10) 2)
    have b26879 := hb (x (-9) 13)
    have b26880 := hb (x (-8) 12)
    clear * - r26874 e26875 e26876 b26877 b26878 b26879 b26880 d26869
    omega
  have d26881 : (x (-9) 5).toNat = 0 := by
    have r26882 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
    have b26883 := hb (x (-9) 5)
    have b26884 := hb (x (-9) 13)
    clear * - r26882 b26883 b26884 d26873
    omega
  have d26885 : (x (-9) 5 && x (-9) 14).toNat = 0 := by
    have r26886 := hand1 (x (-9) 5) (x (-9) 14)
    have b26887 := hb (x (-9) 5)
    have b26888 := hb (x (-9) 5 && x (-9) 14)
    clear * - r26886 b26887 b26888 d26881
    omega
  have d26889 : (x (-10) 6).toNat = 1 := by
    have r26890 : 1 ≤ (x (-4) 9).toNat + (x (-5) 1 && x (-5) 10).toNat + (x (-6) 2 && x (-6) 11).toNat + (x (-7) 3 && x (-7) 12).toNat + (x (-8) 4 && x (-8) 13).toNat + (x (-9) 5 && x (-9) 14).toNat + (x (-10) 6).toNat := by have q := hcov9 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26891 := hb (x (-10) 6)
    have b26892 := hb (x (-4) 9)
    have b26893 := hb (x (-5) 1 && x (-5) 10)
    have b26894 := hb (x (-6) 2 && x (-6) 11)
    have b26895 := hb (x (-7) 3 && x (-7) 12)
    have b26896 := hb (x (-8) 4 && x (-8) 13)
    have b26897 := hb (x (-9) 5 && x (-9) 14)
    clear * - r26890 b26891 b26892 b26893 b26894 b26895 b26896 b26897 d26830 d26711 d26288 d26304 d26683 d26885
    omega
  have d26898 : (x (-10) 14).toNat = 1 := by
    have r26899 : (x (-10) 6).toNat ≤ (x (-10) 14).toNat := himp _ _ (hp6 (-10))
    have b26900 := hb (x (-10) 6)
    have b26901 := hb (x (-10) 14)
    clear * - r26899 b26900 b26901 d26889
    omega
  have d26902 : (x (-11) 1).toNat = 0 := by
    have r26903 : (x (-10) 14).toNat + (x (-11) 1).toNat = 1 := by have q := hd14 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26904 := hb (x (-11) 1)
    have b26905 := hb (x (-10) 14)
    clear * - r26903 b26904 b26905 d26898
    omega
  have d26906 : (x (-11) 13).toNat = 0 := by
    have r26907 : (x (-11) 13).toNat ≤ (x (-11) 1).toNat := himp _ _ (hp13 (-11))
    have b26908 := hb (x (-11) 1)
    have b26909 := hb (x (-11) 13)
    clear * - r26907 b26908 b26909 d26902
    omega
  have d26910 : (x (-11) 3 && x (-11) 13).toNat = 0 := by
    have r26911 := hand2 (x (-11) 3) (x (-11) 13)
    have b26912 := hb (x (-11) 13)
    have b26913 := hb (x (-11) 3 && x (-11) 13)
    clear * - r26911 b26912 b26913 d26906
    omega
  have d26914 : (x (-12) 1 && x (-12) 14).toNat = 1 := by
    have r26915 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26916 := hb (x (-13) 2)
    have b26917 := hb (x (-11) 13)
    have b26918 := hb (x (-12) 1 && x (-12) 14)
    clear * - r26915 b26916 b26917 b26918 d26906 d26822
    omega
  have d26919 : (x (-12) 14).toNat = 1 := by
    have r26920 := hand2 (x (-12) 1) (x (-12) 14)
    have b26921 := hb (x (-12) 14)
    have b26922 := hb (x (-12) 1 && x (-12) 14)
    clear * - r26920 b26921 b26922 d26914
    omega
  have d26923 : (x (-13) 1).toNat = 0 := by
    have r26924 : (x (-12) 14).toNat + (x (-13) 1).toNat = 1 := by have q := hd14 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26925 := hb (x (-13) 1)
    have b26926 := hb (x (-12) 14)
    clear * - r26924 b26925 b26926 d26919
    omega
  have d26927 : (x (-13) 1 && x (-13) 14).toNat = 0 := by
    have r26928 := hand1 (x (-13) 1) (x (-13) 14)
    have b26929 := hb (x (-13) 1)
    have b26930 := hb (x (-13) 1 && x (-13) 14)
    clear * - r26928 b26929 b26930 d26923
    omega
  have d26931 : (x (-14) 2).toNat = 1 := by
    have r26932 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := by have q := hcov13 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26933 := hb (x (-14) 2)
    have b26934 := hb (x (-12) 13)
    have b26935 := hb (x (-13) 1 && x (-13) 14)
    clear * - r26932 b26933 b26934 b26935 d26814 d26927
    omega
  have d26936 : (x (-12) 12).toNat = 0 := by
    have r26937 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26938 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
    have e26939 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
    have b26940 := hb (x (-15) 3)
    have b26941 := hb (x (-14) 2)
    have b26942 := hb (x (-13) 13)
    have b26943 := hb (x (-12) 12)
    clear * - r26937 e26938 e26939 b26940 b26941 b26942 b26943 d26931
    omega
  have d26944 : (x (-12) 4).toNat = 0 := by
    have r26945 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
    have b26946 := hb (x (-12) 4)
    have b26947 := hb (x (-12) 12)
    clear * - r26945 b26946 b26947 d26936
    omega
  have d26948 : (x (-12) 4 && x (-12) 14).toNat = 0 := by
    have r26949 := hand1 (x (-12) 4) (x (-12) 14)
    have b26950 := hb (x (-12) 4)
    have b26951 := hb (x (-12) 4 && x (-12) 14)
    clear * - r26949 b26950 b26951 d26944
    omega
  have d26952 : (x (-13) 13).toNat = 0 := by
    have r26953 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26954 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
    have e26955 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
    have b26956 := hb (x (-15) 3)
    have b26957 := hb (x (-14) 2)
    have b26958 := hb (x (-13) 13)
    have b26959 := hb (x (-12) 12)
    clear * - r26953 e26954 e26955 b26956 b26957 b26958 b26959 d26936 d26931
    omega
  have d26960 : (x (-13) 5).toNat = 0 := by
    have r26961 : (x (-13) 5).toNat ≤ (x (-13) 13).toNat := himp _ _ (hp5 (-13))
    have b26962 := hb (x (-13) 5)
    have b26963 := hb (x (-13) 13)
    clear * - r26961 b26962 b26963 d26952
    omega
  have d26964 : (x (-10) 2 && x (-10) 12).toNat = 1 := by
    have r26965 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b26966 := hb (x (-13) 5)
    have b26967 := hb (x (-8) 10)
    have b26968 := hb (x (-9) 1 && x (-9) 11)
    have b26969 := hb (x (-10) 2 && x (-10) 12)
    have b26970 := hb (x (-11) 3 && x (-11) 13)
    have b26971 := hb (x (-12) 4 && x (-12) 14)
    clear * - r26965 b26966 b26967 b26968 b26969 b26970 b26971 d26771 d26787 d26910 d26948 d26960
    omega
  have d26972 : (x (-10) 2).toNat = 1 := by
    have r26973 := hand1 (x (-10) 2) (x (-10) 12)
    have b26974 := hb (x (-10) 2)
    have b26975 := hb (x (-10) 2 && x (-10) 12)
    clear * - r26973 b26974 b26975 d26964
    omega
  have r26976 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e26977 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
  have e26978 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
  have b26979 := hb (x (-11) 3)
  have b26980 := hb (x (-10) 2)
  have b26981 := hb (x (-9) 13)
  have b26982 := hb (x (-8) 12)
  linarith only [r26976, e26977, e26978, b26979, b26980, b26981, b26982, d26869, d26873, d26972]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a110000_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 6).toNat = 0)
    (g1 : (x (-3) 7).toNat = 0)
    (g2 : (x (-2) 6).toNat = 0)
    (g3 : (x (-1) 5).toNat = 0)
    (g4 : (x 0 3).toNat = 1)
    (g5 : (x 0 4).toNat = 1)
    (g6 : (x 0 11).toNat = 0)
    (g7 : (x 1 2).toNat = 0)
    (g8 : (x 1 5).toNat = 0)
    (g9 : (x 1 10).toNat = 0)
    (g10 : (x 2 4).toNat = 0)
    (g11 : (x 2 5).toNat = 0)
    (g12 : (x 3 4).toNat = 0)
    (g13 : (x 0 2 && x 0 6).toNat = 0)
    (g14 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g15 : (x (-2) 4 && x (-2) 8).toNat = 0)
    (g16 : (x (-3) 5 && x (-3) 9).toNat = 0)
    (g17 : (x (-4) 6 && x (-4) 10).toNat = 0)
    (g18 : (x (-5) 7 && x (-5) 11).toNat = 0)
    (g19 : (x 1 2 && x 1 6).toNat = 0)
    (g20 : (x 0 3 && x 0 7).toNat = 0)
    (g21 : (x 0 4 && x 0 8).toNat = 0)
    (g22 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g23 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g24 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g25 : (x 0 2 && x 0 8).toNat = 0)
    (g26 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g27 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g28 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g29 : (x (-4) 6 && x (-4) 12).toNat = 0)
    (g30 : (x (-5) 7 && x (-5) 13).toNat = 0)
    (g31 : (x 1 1 && x 1 10).toNat = 0)
    (g32 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g33 : (x (-2) 4 && x (-2) 13).toNat = 0)
    (g34 : (x (-3) 5 && x (-3) 14).toNat = 0)
    (g35 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g36 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g37 : (x (-3) 3 && x (-3) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d27136 : (x 0 2 && x 0 11).toNat = 0 := by
    have r27137 := hand2 (x 0 2) (x 0 11)
    have b27138 := hb (x 0 11)
    have b27139 := hb (x 0 2 && x 0 11)
    clear * - r27137 b27138 b27139 g6
    omega
  have d27140 : (x (-4) 4).toNat = 1 := by
    have r27141 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27142 := hb (x (-4) 4)
    have b27143 := hb (x 0 11)
    have b27144 := hb (x (-1) 1 && x (-1) 12)
    have b27145 := hb (x (-2) 2 && x (-2) 13)
    have b27146 := hb (x (-3) 3 && x (-3) 14)
    clear * - r27141 b27142 b27143 b27144 b27145 b27146 g6 g35 g36 g37
    omega
  have d27147 : (x (-4) 12).toNat = 1 := by
    have r27148 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have b27149 := hb (x (-4) 4)
    have b27150 := hb (x (-4) 12)
    clear * - r27148 b27149 b27150 d27140
    omega
  have d27151 : (x (-5) 13).toNat = 0 := by
    have r27152 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27153 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e27154 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b27155 := hb (x (-7) 3)
    have b27156 := hb (x (-6) 2)
    have b27157 := hb (x (-5) 13)
    have b27158 := hb (x (-4) 12)
    clear * - r27152 e27153 e27154 b27155 b27156 b27157 b27158 d27147
    omega
  have d27159 : (x (-5) 9 && x (-5) 13).toNat = 0 := by
    have r27160 := hand2 (x (-5) 9) (x (-5) 13)
    have b27161 := hb (x (-5) 13)
    have b27162 := hb (x (-5) 9 && x (-5) 13)
    clear * - r27160 b27161 b27162 d27151
    omega
  have d27163 : (x (-6) 2).toNat = 0 := by
    have r27164 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27165 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e27166 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b27167 := hb (x (-7) 3)
    have b27168 := hb (x (-6) 2)
    have b27169 := hb (x (-5) 13)
    have b27170 := hb (x (-4) 12)
    clear * - r27164 e27165 e27166 b27167 b27168 b27169 b27170 d27147 d27151
    omega
  have d27171 : (x (-6) 10).toNat = 0 := by
    have r27172 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
    have b27173 := hb (x (-6) 2)
    have b27174 := hb (x (-6) 10)
    clear * - r27172 b27173 b27174 d27163
    omega
  have d27175 : (x (-6) 1 && x (-6) 10).toNat = 0 := by
    have r27176 := hand2 (x (-6) 1) (x (-6) 10)
    have b27177 := hb (x (-6) 10)
    have b27178 := hb (x (-6) 1 && x (-6) 10)
    clear * - r27176 b27177 b27178 d27171
    omega
  have d27179 : (x (-7) 3).toNat = 0 := by
    have r27180 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27181 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e27182 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b27183 := hb (x (-7) 3)
    have b27184 := hb (x (-6) 2)
    have b27185 := hb (x (-5) 13)
    have b27186 := hb (x (-4) 12)
    clear * - r27180 e27181 e27182 b27183 b27184 b27185 b27186 d27147 d27151 d27163
    omega
  have d27187 : (x (-7) 11).toNat = 0 := by
    have r27188 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
    have b27189 := hb (x (-7) 3)
    have b27190 := hb (x (-7) 11)
    clear * - r27188 b27189 b27190 d27179
    omega
  have d27191 : (x (-7) 1 && x (-7) 11).toNat = 0 := by
    have r27192 := hand2 (x (-7) 1) (x (-7) 11)
    have b27193 := hb (x (-7) 11)
    have b27194 := hb (x (-7) 1 && x (-7) 11)
    clear * - r27192 b27193 b27194 d27187
    omega
  have d27195 : (x (-7) 2 && x (-7) 11).toNat = 0 := by
    have r27196 := hand2 (x (-7) 2) (x (-7) 11)
    have b27197 := hb (x (-7) 11)
    have b27198 := hb (x (-7) 2 && x (-7) 11)
    clear * - r27196 b27197 b27198 d27187
    omega
  have d27199 : (x 2 9).toNat = 1 := by
    have r27200 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b27201 := hb (x (-4) 6)
    have b27202 := hb (x 2 9)
    have b27203 := hb (x 1 1 && x 1 10)
    have b27204 := hb (x 0 2 && x 0 11)
    have b27205 := hb (x (-1) 3 && x (-1) 12)
    have b27206 := hb (x (-2) 4 && x (-2) 13)
    have b27207 := hb (x (-3) 5 && x (-3) 14)
    clear * - r27200 b27201 b27202 b27203 b27204 b27205 b27206 b27207 g31 d27136 g32 g33 g34 g0
    omega
  have d27208 : (x 2 1).toNat = 1 := by
    have r27209 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
    have b27210 := hb (x 2 1)
    have b27211 := hb (x 2 9)
    clear * - r27209 b27210 b27211 d27199
    omega
  have d27212 : (x 3 8).toNat = 0 := by
    have r27213 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27214 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e27215 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e27216 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e27217 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e27218 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e27219 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b27220 := hb (x (-4) 7)
    have b27221 := hb (x (-3) 6)
    have b27222 := hb (x (-2) 5)
    have b27223 := hb (x (-1) 4)
    have b27224 := hb (x 0 11)
    have b27225 := hb (x 1 10)
    have b27226 := hb (x 2 9)
    have b27227 := hb (x 3 8)
    clear * - r27213 e27214 e27215 e27216 e27217 e27218 e27219 b27220 b27221 b27222 b27223 b27224 b27225 b27226 b27227 d27199 g9 g6
    omega
  have d27228 : (x (-1) 4).toNat = 0 := by
    have r27229 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27230 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e27231 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e27232 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e27233 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e27234 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e27235 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b27236 := hb (x (-4) 7)
    have b27237 := hb (x (-3) 6)
    have b27238 := hb (x (-2) 5)
    have b27239 := hb (x (-1) 4)
    have b27240 := hb (x 0 11)
    have b27241 := hb (x 1 10)
    have b27242 := hb (x 2 9)
    have b27243 := hb (x 3 8)
    clear * - r27229 e27230 e27231 e27232 e27233 e27234 e27235 b27236 b27237 b27238 b27239 b27240 b27241 b27242 b27243 d27212 d27199 g9 g6
    omega
  have d27244 : (x (-1) 4 && x (-1) 8).toNat = 0 := by
    have r27245 := hand1 (x (-1) 4) (x (-1) 8)
    have b27246 := hb (x (-1) 4)
    have b27247 := hb (x (-1) 4 && x (-1) 8)
    clear * - r27245 b27246 b27247 d27228
    omega
  have d27248 : (x (-2) 5).toNat = 0 := by
    have r27249 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27250 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e27251 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e27252 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e27253 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e27254 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e27255 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b27256 := hb (x (-4) 7)
    have b27257 := hb (x (-3) 6)
    have b27258 := hb (x (-2) 5)
    have b27259 := hb (x (-1) 4)
    have b27260 := hb (x 0 11)
    have b27261 := hb (x 1 10)
    have b27262 := hb (x 2 9)
    have b27263 := hb (x 3 8)
    clear * - r27249 e27250 e27251 e27252 e27253 e27254 e27255 b27256 b27257 b27258 b27259 b27260 b27261 b27262 b27263 d27212 d27199 g9 g6 d27228
    omega
  have d27264 : (x (-2) 5 && x (-2) 9).toNat = 0 := by
    have r27265 := hand1 (x (-2) 5) (x (-2) 9)
    have b27266 := hb (x (-2) 5)
    have b27267 := hb (x (-2) 5 && x (-2) 9)
    clear * - r27265 b27266 b27267 d27248
    omega
  have d27268 : (x (-3) 6).toNat = 0 := by
    have r27269 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27270 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e27271 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e27272 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e27273 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e27274 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e27275 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b27276 := hb (x (-4) 7)
    have b27277 := hb (x (-3) 6)
    have b27278 := hb (x (-2) 5)
    have b27279 := hb (x (-1) 4)
    have b27280 := hb (x 0 11)
    have b27281 := hb (x 1 10)
    have b27282 := hb (x 2 9)
    have b27283 := hb (x 3 8)
    clear * - r27269 e27270 e27271 e27272 e27273 e27274 e27275 b27276 b27277 b27278 b27279 b27280 b27281 b27282 b27283 d27212 d27199 g9 g6 d27228 d27248
    omega
  have d27284 : (x (-3) 6 && x (-3) 10).toNat = 0 := by
    have r27285 := hand1 (x (-3) 6) (x (-3) 10)
    have b27286 := hb (x (-3) 6)
    have b27287 := hb (x (-3) 6 && x (-3) 10)
    clear * - r27285 b27286 b27287 d27268
    omega
  have d27288 : (x (-4) 7).toNat = 0 := by
    have r27289 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e27290 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
    have e27291 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
    have e27292 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
    have e27293 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
    have e27294 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
    have e27295 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
    have b27296 := hb (x (-4) 7)
    have b27297 := hb (x (-3) 6)
    have b27298 := hb (x (-2) 5)
    have b27299 := hb (x (-1) 4)
    have b27300 := hb (x 0 11)
    have b27301 := hb (x 1 10)
    have b27302 := hb (x 2 9)
    have b27303 := hb (x 3 8)
    clear * - r27289 e27290 e27291 e27292 e27293 e27294 e27295 b27296 b27297 b27298 b27299 b27300 b27301 b27302 b27303 d27212 d27199 g9 g6 d27228 d27248 d27268
    omega
  have d27304 : (x (-4) 7 && x (-4) 11).toNat = 0 := by
    have r27305 := hand1 (x (-4) 7) (x (-4) 11)
    have b27306 := hb (x (-4) 7)
    have b27307 := hb (x (-4) 7 && x (-4) 11)
    clear * - r27305 b27306 b27307 d27288
    omega
  have r27308 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r27309 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r27310 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e27311 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
  have e27312 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
  have e27313 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
  have e27314 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
  have e27315 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
  have e27316 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
  have r27317 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e27318 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
  have e27319 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
  have e27320 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
  have e27321 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
  have e27322 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
  have e27323 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
  have r27324 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e27325 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
  have e27326 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
  have e27327 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
  have e27328 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
  have e27329 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
  have e27330 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
  have r27331 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e27332 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
  have e27333 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
  have r27334 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e27335 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
  have e27336 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
  have r27337 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e27338 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
  have e27339 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
  have r27340 : 1 ≤ (x 4 4).toNat + (x 3 1 && x 3 5).toNat + (x 2 2 && x 2 6).toNat + (x 1 3 && x 1 7).toNat + (x 0 4 && x 0 8).toNat + (x (-1) 5 && x (-1) 9).toNat + (x (-2) 6 && x (-2) 10).toNat + (x (-3) 7 && x (-3) 11).toNat + (x (-4) 8 && x (-4) 12).toNat + (x (-5) 9 && x (-5) 13).toNat + (x (-6) 10 && x (-6) 14).toNat + (x (-7) 11).toNat := by have q := hcov4 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e27341 : (x 3 1 && x 3 5).toNat = (x 3 5).toNat := handr _ _ (fun h => hp13 3 (hp5 3 (h)))
  have e27342 : (x (-6) 10 && x (-6) 14).toNat = (x (-6) 10).toNat := handl _ _ (fun h => hp2 (-6) (hp10 (-6) (h)))
  have r27343 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r27344 : 1 ≤ (x (-5) 9).toNat + (x (-6) 1 && x (-6) 10).toNat + (x (-7) 2 && x (-7) 11).toNat + (x (-8) 3 && x (-8) 12).toNat + (x (-9) 4 && x (-9) 13).toNat + (x (-10) 5 && x (-10) 14).toNat + (x (-11) 6).toNat := by have q := hcov9 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r27345 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r27346 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have r27347 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
  have r27348 := hand2 (x (-6) 8) (x (-6) 12)
  have r27349 := hand2 (x (-7) 9) (x (-7) 13)
  have r27350 := hand1 (x (-5) 8) (x (-5) 12)
  have r27351 := hand1 (x (-6) 9) (x (-6) 13)
  have r27352 := hand1 (x 2 2) (x 2 6)
  have r27353 := hand1 (x 1 3) (x 1 7)
  have r27354 := hand1 (x (-4) 8) (x (-4) 12)
  have r27355 := hand2 (x 1 1) (x 1 7)
  have r27356 := hand1 (x (-6) 8) (x (-6) 14)
  have r27357 := hand2 (x (-8) 3) (x (-8) 12)
  have r27358 := hand1 (x (-9) 4) (x (-9) 13)
  have r27359 := hand1 (x (-10) 5) (x (-10) 14)
  have r27360 := hand1 (x (-8) 2) (x (-8) 12)
  have r27361 := hand1 (x (-9) 3) (x (-9) 13)
  have r27362 := hand1 (x (-10) 4) (x (-10) 14)
  have r27363 := hand2 (x (-10) 1) (x (-10) 14)
  linarith only [r27308, r27309, r27310, e27311, e27312, e27313, e27314, e27315, e27316, r27317, e27318, e27319, e27320, e27321, e27322, e27323, r27324, e27325, e27326, e27327, e27328, e27329, e27330, r27331, e27332, e27333, r27334, e27335, e27336, r27337, e27338, e27339, r27340, e27341, e27342, r27343, r27344, r27345, r27346, r27347, r27348, r27349, r27350, r27351, r27352, r27353, r27354, r27355, r27356, r27357, r27358, r27359, r27360, r27361, r27362, r27363, d27187, d27171, d27288, d27268, g1, d27248, g2, d27228, g3, g4, g5, g7, g8, d27208, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, d27244, d27264, d27284, d27304, g21, g22, g23, g24, d27159, g25, g26, g27, g28, g29, g30, d27175, d27195, d27191]

theorem cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a110000 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 6).toNat = 0)
    (g1 : (x (-3) 7).toNat = 0)
    (g2 : (x (-2) 6).toNat = 0)
    (g3 : (x (-1) 5).toNat = 0)
    (g4 : (x 0 3).toNat = 1)
    (g5 : (x 0 4).toNat = 1)
    (g6 : (x 0 11).toNat = 0)
    (g7 : (x 1 2).toNat = 0)
    (g8 : (x 1 5).toNat = 0)
    (g9 : (x 1 10).toNat = 0)
    (g10 : (x 2 4).toNat = 0)
    (g11 : (x 2 5).toNat = 0)
    (g12 : (x 3 4).toNat = 0)
    (g13 : (x 0 2 && x 0 6).toNat = 0)
    (g14 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g15 : (x (-2) 4 && x (-2) 8).toNat = 0)
    (g16 : (x (-3) 5 && x (-3) 9).toNat = 0)
    (g17 : (x (-4) 6 && x (-4) 10).toNat = 0)
    (g18 : (x (-5) 7 && x (-5) 11).toNat = 0)
    (g19 : (x 1 2 && x 1 6).toNat = 0)
    (g20 : (x 0 3 && x 0 7).toNat = 0)
    (g21 : (x 0 4 && x 0 8).toNat = 0)
    (g22 : (x (-1) 5 && x (-1) 9).toNat = 0)
    (g23 : (x (-2) 6 && x (-2) 10).toNat = 0)
    (g24 : (x (-3) 7 && x (-3) 11).toNat = 0)
    (g25 : (x 0 2 && x 0 8).toNat = 0)
    (g26 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g27 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g28 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g29 : (x (-4) 6 && x (-4) 12).toNat = 0)
    (g30 : (x (-5) 7 && x (-5) 13).toNat = 0)
    (g31 : (x 1 1 && x 1 10).toNat = 0)
    (g32 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g33 : (x (-2) 4 && x (-2) 13).toNat = 0)
    (g34 : (x (-3) 5 && x (-3) 14).toNat = 0)
    (g35 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g36 : (x (-2) 2 && x (-2) 13).toNat = 0)
    (g37 : (x (-3) 3 && x (-3) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_four_iff_five_core_a110000_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37
