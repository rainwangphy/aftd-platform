import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a01110

Topic: combinatorics   Node: cbab612c6eb2

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core: under the layer-free tight-cover constraints for k = 15 and 37 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a0110.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a0110 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-1) 13).toNat = 0)
    (g1 : (x 0 1).toNat = 0)
    (g2 : (x 1 13).toNat = 0)
    (g3 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g4 : (x (-1) 3 && x (-1) 14).toNat = 0)
    (g5 : (x 2 1 && x 2 12).toNat = 0)
    (g6 : (x 1 2 && x 1 13).toNat = 0)
    (g7 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d47250 : (x 0 1 && x 0 14).toNat = 0 := by
    have r47251 := hand1 (x 0 1) (x 0 14)
    have b47252 := hb (x 0 1)
    have b47253 := hb (x 0 1 && x 0 14)
    clear * - r47251 b47252 b47253 g1
    omega
  have d47254 : (x 0 1 && x 0 12).toNat = 0 := by
    have r47255 := hand1 (x 0 1) (x 0 12)
    have b47256 := hb (x 0 1)
    have b47257 := hb (x 0 1 && x 0 12)
    clear * - r47255 b47256 b47257 g1
    omega
  have d47258 : (x 0 13).toNat = 0 := by
    have r47259 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
    have b47260 := hb (x 0 1)
    have b47261 := hb (x 0 13)
    clear * - r47259 b47260 b47261 g1
    omega
  have d47262 : (x 0 2 && x 0 13).toNat = 0 := by
    have r47263 := hand2 (x 0 2) (x 0 13)
    have b47264 := hb (x 0 13)
    have b47265 := hb (x 0 2 && x 0 13)
    clear * - r47263 b47264 b47265 d47258
    omega
  have d47266 : (x (-1) 2).toNat = 1 := by
    have r47267 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47268 := hb (x (-1) 2)
    have b47269 := hb (x 1 13)
    have b47270 := hb (x 0 1 && x 0 14)
    clear * - r47267 b47268 b47269 b47270 g2 d47250
    omega
  have d47271 : (x (-1) 14).toNat = 1 := by
    have r47272 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have b47273 := hb (x (-1) 2)
    have b47274 := hb (x (-1) 14)
    clear * - r47272 b47273 b47274 d47266
    omega
  have d47275 : (x (-2) 1).toNat = 0 := by
    have r47276 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47277 := hb (x (-2) 1)
    have b47278 := hb (x (-1) 14)
    clear * - r47276 b47277 b47278 d47271
    omega
  have d47279 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r47280 := hand1 (x (-2) 1) (x (-2) 14)
    have b47281 := hb (x (-2) 1)
    have b47282 := hb (x (-2) 1 && x (-2) 14)
    clear * - r47280 b47281 b47282 d47275
    omega
  have d47283 : (x (-2) 13).toNat = 0 := by
    have r47284 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b47285 := hb (x (-2) 1)
    have b47286 := hb (x (-2) 13)
    clear * - r47284 b47285 b47286 d47275
    omega
  have d47287 : (x (-2) 2).toNat = 1 := by
    have r47288 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47289 := hb (x (-2) 2)
    have b47290 := hb (x 0 13)
    have b47291 := hb (x (-1) 1 && x (-1) 14)
    clear * - r47288 b47289 b47290 b47291 d47258 g7
    omega
  have d47292 : (x (-2) 14).toNat = 1 := by
    have r47293 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
    have b47294 := hb (x (-2) 2)
    have b47295 := hb (x (-2) 14)
    clear * - r47293 b47294 b47295 d47287
    omega
  have d47296 : (x (-3) 1).toNat = 0 := by
    have r47297 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47298 := hb (x (-3) 1)
    have b47299 := hb (x (-2) 14)
    clear * - r47297 b47298 b47299 d47292
    omega
  have d47300 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
    have r47301 := hand1 (x (-3) 1) (x (-3) 14)
    have b47302 := hb (x (-3) 1)
    have b47303 := hb (x (-3) 1 && x (-3) 14)
    clear * - r47301 b47302 b47303 d47296
    omega
  have d47304 : (x (-3) 13).toNat = 0 := by
    have r47305 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b47306 := hb (x (-3) 1)
    have b47307 := hb (x (-3) 13)
    clear * - r47305 b47306 b47307 d47296
    omega
  have d47308 : (x (-3) 2).toNat = 1 := by
    have r47309 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47310 := hb (x (-3) 2)
    have b47311 := hb (x (-1) 13)
    have b47312 := hb (x (-2) 1 && x (-2) 14)
    clear * - r47309 b47310 b47311 b47312 g0 d47279
    omega
  have d47313 : (x (-3) 14).toNat = 1 := by
    have r47314 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b47315 := hb (x (-3) 2)
    have b47316 := hb (x (-3) 14)
    clear * - r47314 b47315 b47316 d47308
    omega
  have d47317 : (x (-4) 1).toNat = 0 := by
    have r47318 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47319 := hb (x (-4) 1)
    have b47320 := hb (x (-3) 14)
    clear * - r47318 b47319 b47320 d47313
    omega
  have d47321 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r47322 := hand1 (x (-4) 1) (x (-4) 14)
    have b47323 := hb (x (-4) 1)
    have b47324 := hb (x (-4) 1 && x (-4) 14)
    clear * - r47322 b47323 b47324 d47317
    omega
  have d47325 : (x (-4) 13).toNat = 0 := by
    have r47326 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b47327 := hb (x (-4) 1)
    have b47328 := hb (x (-4) 13)
    clear * - r47326 b47327 b47328 d47317
    omega
  have d47329 : (x (-4) 2).toNat = 1 := by
    have r47330 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47331 := hb (x (-4) 2)
    have b47332 := hb (x (-2) 13)
    have b47333 := hb (x (-3) 1 && x (-3) 14)
    clear * - r47330 b47331 b47332 b47333 d47283 d47300
    omega
  have d47334 : (x (-5) 2).toNat = 1 := by
    have r47335 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47336 := hb (x (-5) 2)
    have b47337 := hb (x (-3) 13)
    have b47338 := hb (x (-4) 1 && x (-4) 14)
    clear * - r47335 b47336 b47337 b47338 d47304 d47321
    omega
  have d47339 : (x 1 12).toNat = 0 := by
    have r47340 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47341 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e47342 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b47343 := hb (x (-2) 3)
    have b47344 := hb (x (-1) 2)
    have b47345 := hb (x 0 13)
    have b47346 := hb (x 1 12)
    clear * - r47340 e47341 e47342 b47343 b47344 b47345 b47346 d47258 d47266
    omega
  have d47347 : (x 1 1 && x 1 12).toNat = 0 := by
    have r47348 := hand2 (x 1 1) (x 1 12)
    have b47349 := hb (x 1 12)
    have b47350 := hb (x 1 1 && x 1 12)
    clear * - r47348 b47349 b47350 d47339
    omega
  have d47351 : (x (-2) 3).toNat = 0 := by
    have r47352 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47353 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e47354 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b47355 := hb (x (-2) 3)
    have b47356 := hb (x (-1) 2)
    have b47357 := hb (x 0 13)
    have b47358 := hb (x 1 12)
    clear * - r47352 e47353 e47354 b47355 b47356 b47357 b47358 d47339 d47258 d47266
    omega
  have d47359 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
    have r47360 := hand1 (x (-2) 3) (x (-2) 14)
    have b47361 := hb (x (-2) 3)
    have b47362 := hb (x (-2) 3 && x (-2) 14)
    clear * - r47360 b47361 b47362 d47351
    omega
  have d47363 : (x (-1) 12).toNat = 0 := by
    have r47364 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47365 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e47366 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b47367 := hb (x (-4) 3)
    have b47368 := hb (x (-3) 2)
    have b47369 := hb (x (-2) 13)
    have b47370 := hb (x (-1) 12)
    clear * - r47364 e47365 e47366 b47367 b47368 b47369 b47370 d47283 d47308
    omega
  have d47371 : (x (-1) 4).toNat = 0 := by
    have r47372 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
    have b47373 := hb (x (-1) 4)
    have b47374 := hb (x (-1) 12)
    clear * - r47372 b47373 b47374 d47363
    omega
  have d47375 : (x (-2) 12).toNat = 0 := by
    have r47376 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47377 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e47378 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have b47379 := hb (x (-5) 3)
    have b47380 := hb (x (-4) 2)
    have b47381 := hb (x (-3) 13)
    have b47382 := hb (x (-2) 12)
    clear * - r47376 e47377 e47378 b47379 b47380 b47381 b47382 d47304 d47329
    omega
  have d47383 : (x (-2) 4).toNat = 0 := by
    have r47384 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
    have b47385 := hb (x (-2) 4)
    have b47386 := hb (x (-2) 12)
    clear * - r47384 b47385 b47386 d47375
    omega
  have d47387 : (x (-3) 12).toNat = 0 := by
    have r47388 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47389 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e47390 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b47391 := hb (x (-6) 3)
    have b47392 := hb (x (-5) 2)
    have b47393 := hb (x (-4) 13)
    have b47394 := hb (x (-3) 12)
    clear * - r47388 e47389 e47390 b47391 b47392 b47393 b47394 d47325 d47334
    omega
  have d47395 : (x (-3) 4).toNat = 0 := by
    have r47396 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
    have b47397 := hb (x (-3) 4)
    have b47398 := hb (x (-3) 12)
    clear * - r47396 b47397 b47398 d47387
    omega
  have d47399 : (x 2 11).toNat = 1 := by
    have r47400 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47401 := hb (x (-2) 4)
    have b47402 := hb (x 2 11)
    have b47403 := hb (x 1 1 && x 1 12)
    have b47404 := hb (x 0 2 && x 0 13)
    have b47405 := hb (x (-1) 3 && x (-1) 14)
    clear * - r47400 b47401 b47402 b47403 b47404 b47405 d47347 d47262 g4 d47383
    omega
  have d47406 : (x 2 3).toNat = 1 := by
    have r47407 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
    have b47408 := hb (x 2 3)
    have b47409 := hb (x 2 11)
    clear * - r47407 b47408 b47409 d47399
    omega
  have d47410 : (x 5 12).toNat = 0 := by
    have r47411 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47412 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e47413 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b47414 := hb (x 2 3)
    have b47415 := hb (x 3 2)
    have b47416 := hb (x 4 13)
    have b47417 := hb (x 5 12)
    clear * - r47411 e47412 e47413 b47414 b47415 b47416 b47417 d47406
    omega
  have d47418 : (x 4 13).toNat = 0 := by
    have r47419 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47420 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e47421 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b47422 := hb (x 2 3)
    have b47423 := hb (x 3 2)
    have b47424 := hb (x 4 13)
    have b47425 := hb (x 5 12)
    clear * - r47419 e47420 e47421 b47422 b47423 b47424 b47425 d47410 d47406
    omega
  have d47426 : (x 3 2).toNat = 0 := by
    have r47427 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47428 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e47429 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b47430 := hb (x 2 3)
    have b47431 := hb (x 3 2)
    have b47432 := hb (x 4 13)
    have b47433 := hb (x 5 12)
    clear * - r47427 e47428 e47429 b47430 b47431 b47432 b47433 d47410 d47418 d47406
    omega
  have d47434 : (x 1 11).toNat = 1 := by
    have r47435 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47436 := hb (x (-3) 4)
    have b47437 := hb (x 1 11)
    have b47438 := hb (x 0 1 && x 0 12)
    have b47439 := hb (x (-1) 2 && x (-1) 13)
    have b47440 := hb (x (-2) 3 && x (-2) 14)
    clear * - r47435 b47436 b47437 b47438 b47439 b47440 d47254 g3 d47359 d47395
    omega
  have d47441 : (x 1 3).toNat = 1 := by
    have r47442 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b47443 := hb (x 1 3)
    have b47444 := hb (x 1 11)
    clear * - r47442 b47443 b47444 d47434
    omega
  have d47445 : (x 4 12).toNat = 0 := by
    have r47446 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47447 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e47448 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b47449 := hb (x 1 3)
    have b47450 := hb (x 2 2)
    have b47451 := hb (x 3 13)
    have b47452 := hb (x 4 12)
    clear * - r47446 e47447 e47448 b47449 b47450 b47451 b47452 d47441
    omega
  have d47453 : (x 3 13).toNat = 0 := by
    have r47454 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47455 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e47456 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b47457 := hb (x 1 3)
    have b47458 := hb (x 2 2)
    have b47459 := hb (x 3 13)
    have b47460 := hb (x 4 12)
    clear * - r47454 e47455 e47456 b47457 b47458 b47459 b47460 d47445 d47441
    omega
  have d47461 : (x 2 2).toNat = 0 := by
    have r47462 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47463 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e47464 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b47465 := hb (x 1 3)
    have b47466 := hb (x 2 2)
    have b47467 := hb (x 3 13)
    have b47468 := hb (x 4 12)
    clear * - r47462 e47463 e47464 b47465 b47466 b47467 b47468 d47445 d47453 d47441
    omega
  have d47469 : (x 3 1 && x 3 14).toNat = 1 := by
    have r47470 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47471 := hb (x 2 2)
    have b47472 := hb (x 4 13)
    have b47473 := hb (x 3 1 && x 3 14)
    clear * - r47470 b47471 b47472 b47473 d47418 d47461
    omega
  have d47474 : (x 3 14).toNat = 1 := by
    have r47475 := hand2 (x 3 1) (x 3 14)
    have b47476 := hb (x 3 14)
    have b47477 := hb (x 3 1 && x 3 14)
    clear * - r47475 b47476 b47477 d47469
    omega
  have d47478 : (x 2 1).toNat = 0 := by
    have r47479 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47480 := hb (x 2 1)
    have b47481 := hb (x 3 14)
    clear * - r47479 b47480 b47481 d47474
    omega
  have d47482 : (x 2 1 && x 2 14).toNat = 0 := by
    have r47483 := hand1 (x 2 1) (x 2 14)
    have b47484 := hb (x 2 1)
    have b47485 := hb (x 2 1 && x 2 14)
    clear * - r47483 b47484 b47485 d47478
    omega
  have d47486 : (x 1 2).toNat = 1 := by
    have r47487 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47488 := hb (x 1 2)
    have b47489 := hb (x 3 13)
    have b47490 := hb (x 2 1 && x 2 14)
    clear * - r47487 b47488 b47489 b47490 d47453 d47482
    omega
  have d47491 : (x 3 12).toNat = 0 := by
    have r47492 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47493 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e47494 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b47495 := hb (x 0 3)
    have b47496 := hb (x 1 2)
    have b47497 := hb (x 2 13)
    have b47498 := hb (x 3 12)
    clear * - r47492 e47493 e47494 b47495 b47496 b47497 b47498 d47486
    omega
  have d47499 : (x 2 13).toNat = 0 := by
    have r47500 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47501 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e47502 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b47503 := hb (x 0 3)
    have b47504 := hb (x 1 2)
    have b47505 := hb (x 2 13)
    have b47506 := hb (x 3 12)
    clear * - r47500 e47501 e47502 b47503 b47504 b47505 b47506 d47491 d47486
    omega
  have d47507 : (x 0 3).toNat = 0 := by
    have r47508 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47509 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e47510 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b47511 := hb (x 0 3)
    have b47512 := hb (x 1 2)
    have b47513 := hb (x 2 13)
    have b47514 := hb (x 3 12)
    clear * - r47508 e47509 e47510 b47511 b47512 b47513 b47514 d47491 d47499 d47486
    omega
  have d47515 : (x 0 3 && x 0 14).toNat = 0 := by
    have r47516 := hand1 (x 0 3) (x 0 14)
    have b47517 := hb (x 0 3)
    have b47518 := hb (x 0 3 && x 0 14)
    clear * - r47516 b47517 b47518 d47507
    omega
  have d47519 : (x 3 11).toNat = 1 := by
    have r47520 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47521 := hb (x (-1) 4)
    have b47522 := hb (x 3 11)
    have b47523 := hb (x 2 1 && x 2 12)
    have b47524 := hb (x 1 2 && x 1 13)
    have b47525 := hb (x 0 3 && x 0 14)
    clear * - r47520 b47521 b47522 b47523 b47524 b47525 g5 g6 d47515 d47371
    omega
  have d47526 : (x 3 3).toNat = 1 := by
    have r47527 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b47528 := hb (x 3 3)
    have b47529 := hb (x 3 11)
    clear * - r47527 b47528 b47529 d47519
    omega
  have d47530 : (x 6 12).toNat = 0 := by
    have r47531 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47532 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e47533 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b47534 := hb (x 3 3)
    have b47535 := hb (x 4 2)
    have b47536 := hb (x 5 13)
    have b47537 := hb (x 6 12)
    clear * - r47531 e47532 e47533 b47534 b47535 b47536 b47537 d47526
    omega
  have d47538 : (x 5 13).toNat = 0 := by
    have r47539 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e47540 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e47541 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b47542 := hb (x 3 3)
    have b47543 := hb (x 4 2)
    have b47544 := hb (x 5 13)
    have b47545 := hb (x 6 12)
    clear * - r47539 e47540 e47541 b47542 b47543 b47544 b47545 d47530 d47526
    omega
  have d47546 : (x 4 1 && x 4 14).toNat = 1 := by
    have r47547 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47548 := hb (x 3 2)
    have b47549 := hb (x 5 13)
    have b47550 := hb (x 4 1 && x 4 14)
    clear * - r47547 b47548 b47549 b47550 d47538 d47426
    omega
  have d47551 : (x 4 14).toNat = 1 := by
    have r47552 := hand2 (x 4 1) (x 4 14)
    have b47553 := hb (x 4 14)
    have b47554 := hb (x 4 1 && x 4 14)
    clear * - r47552 b47553 b47554 d47546
    omega
  have d47555 : (x 3 1).toNat = 0 := by
    have r47556 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b47557 := hb (x 3 1)
    have b47558 := hb (x 4 14)
    clear * - r47556 b47557 b47558 d47551
    omega
  have r47559 := hand1 (x 3 1) (x 3 14)
  have b47560 := hb (x 3 1)
  have b47561 := hb (x 3 1 && x 3 14)
  linarith only [r47559, b47560, b47561, d47469, d47555]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a01110_aux (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-5) 5).toNat = 0)
    (g2 : (x (-4) 4).toNat = 0)
    (g3 : (x (-2) 10).toNat = 0)
    (g4 : (x (-1) 3).toNat = 0)
    (g5 : (x (-1) 5).toNat = 0)
    (g6 : (x (-1) 11).toNat = 0)
    (g7 : (x (-1) 13).toNat = 0)
    (g8 : (x 0 1).toNat = 1)
    (g9 : (x 0 2).toNat = 1)
    (g10 : (x 0 3).toNat = 0)
    (g11 : (x 0 9).toNat = 0)
    (g12 : (x 1 2).toNat = 0)
    (g13 : (x 1 5).toNat = 0)
    (g14 : (x 1 10).toNat = 0)
    (g15 : (x 2 4).toNat = 0)
    (g16 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g17 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g18 : (x (-4) 4 && x (-4) 13).toNat = 0)
    (g19 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g20 : (x 1 1 && x 1 10).toNat = 0)
    (g21 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g22 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g23 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g24 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g25 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g26 : (x 1 2 && x 1 12).toNat = 0)
    (g27 : (x 2 2 && x 2 12).toNat = 0)
    (g28 : (x 1 3 && x 1 13).toNat = 0)
    (g29 : (x 1 4 && x 1 14).toNat = 0)
    (g30 : (x 2 4 && x 2 14).toNat = 0)
    (g31 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g32 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g33 : (x (-1) 3 && x (-1) 14).toNat = 0)
    (g34 : (x 2 1 && x 2 12).toNat = 0)
    (g35 : (x 1 2 && x 1 13).toNat = 0)
    (g36 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d47609 : (x 0 3 && x 0 14).toNat = 0 := by
    have r47610 := hand1 (x 0 3) (x 0 14)
    have b47611 := hb (x 0 3)
    have b47612 := hb (x 0 3 && x 0 14)
    clear * - r47610 b47611 b47612 g10
    omega
  have d47613 : (x 0 3 && x 0 13).toNat = 0 := by
    have r47614 := hand1 (x 0 3) (x 0 13)
    have b47615 := hb (x 0 3)
    have b47616 := hb (x 0 3 && x 0 13)
    clear * - r47614 b47615 b47616 g10
    omega
  have d47617 : (x 0 11).toNat = 0 := by
    have r47618 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
    have b47619 := hb (x 0 3)
    have b47620 := hb (x 0 11)
    clear * - r47618 b47619 b47620 g10
    omega
  have d47621 : (x 0 1 && x 0 11).toNat = 0 := by
    have r47622 := hand2 (x 0 1) (x 0 11)
    have b47623 := hb (x 0 11)
    have b47624 := hb (x 0 1 && x 0 11)
    clear * - r47622 b47623 b47624 d47617
    omega
  have d47625 : (x 0 2 && x 0 11).toNat = 0 := by
    have r47626 := hand2 (x 0 2) (x 0 11)
    have b47627 := hb (x 0 11)
    have b47628 := hb (x 0 2 && x 0 11)
    clear * - r47626 b47627 b47628 d47617
    omega
  cases h47629 : x 0 4
  · have f47630 : (x 0 4).toNat = 0 := by rw [h47629]; rfl
    have d47631 : (x 0 4 && x 0 14).toNat = 0 := by
      have r47632 := hand1 (x 0 4) (x 0 14)
      have b47633 := hb (x 0 4)
      have b47634 := hb (x 0 4 && x 0 14)
      clear * - r47632 b47633 b47634 f47630
      omega
    cases h47635 : x 0 5
    · have f47636 : (x 0 5).toNat = 0 := by rw [h47635]; rfl
      cases h47637 : x 0 6
      · have f47638 : (x 0 6).toNat = 0 := by rw [h47637]; rfl
        have d47639 : (x 0 1 && x 0 6).toNat = 0 := by
          have r47640 := hand2 (x 0 1) (x 0 6)
          have b47641 := hb (x 0 6)
          have b47642 := hb (x 0 1 && x 0 6)
          clear * - r47640 b47641 b47642 f47638
          omega
        have d47643 : (x 0 2 && x 0 6).toNat = 0 := by
          have r47644 := hand2 (x 0 2) (x 0 6)
          have b47645 := hb (x 0 6)
          have b47646 := hb (x 0 2 && x 0 6)
          clear * - r47644 b47645 b47646 f47638
          omega
        cases h47647 : x 0 10
        · have f47648 : (x 0 10).toNat = 0 := by rw [h47647]; rfl
          cases h47649 : x 0 12
          · have f47650 : (x 0 12).toNat = 0 := by rw [h47649]; rfl
            have d47651 : (x 0 1 && x 0 12).toNat = 0 := by
              have r47652 := hand2 (x 0 1) (x 0 12)
              have b47653 := hb (x 0 12)
              have b47654 := hb (x 0 1 && x 0 12)
              clear * - r47652 b47653 b47654 f47650
              omega
            have d47655 : (x 0 2 && x 0 12).toNat = 0 := by
              have r47656 := hand2 (x 0 2) (x 0 12)
              have b47657 := hb (x 0 12)
              have b47658 := hb (x 0 2 && x 0 12)
              clear * - r47656 b47657 b47658 f47650
              omega
            cases h47659 : x 1 1
            · have f47660 : (x 1 1).toNat = 0 := by rw [h47659]; rfl
              have d47661 : (x 1 1 && x 1 12).toNat = 0 := by
                have r47662 := hand1 (x 1 1) (x 1 12)
                have b47663 := hb (x 1 1)
                have b47664 := hb (x 1 1 && x 1 12)
                clear * - r47662 b47663 b47664 f47660
                omega
              have d47665 : (x 1 1 && x 1 11).toNat = 0 := by
                have r47666 := hand1 (x 1 1) (x 1 11)
                have b47667 := hb (x 1 1)
                have b47668 := hb (x 1 1 && x 1 11)
                clear * - r47666 b47667 b47668 f47660
                omega
              cases h47669 : x (-1) 2
              · have f47670 : (x (-1) 2).toNat = 0 := by rw [h47669]; rfl
                have d47671 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
                  have r47672 := hand1 (x (-1) 2) (x (-1) 7)
                  have b47673 := hb (x (-1) 2)
                  have b47674 := hb (x (-1) 2 && x (-1) 7)
                  clear * - r47672 b47673 b47674 f47670
                  omega
                cases h47675 : x 1 3
                · have f47676 : (x 1 3).toNat = 0 := by rw [h47675]; rfl
                  have d47677 : (x 1 11).toNat = 0 := by
                    have r47678 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
                    have b47679 := hb (x 1 3)
                    have b47680 := hb (x 1 11)
                    clear * - r47678 b47679 b47680 f47676
                    omega
                  cases h47681 : x (-1) 4
                  · have f47682 : (x (-1) 4).toNat = 0 := by rw [h47681]; rfl
                    have d47683 : (x 3 11).toNat = 1 := by
                      have r47684 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47685 := hb (x (-1) 4)
                      have b47686 := hb (x 3 11)
                      have b47687 := hb (x 2 1 && x 2 12)
                      have b47688 := hb (x 1 2 && x 1 13)
                      have b47689 := hb (x 0 3 && x 0 14)
                      clear * - r47684 b47685 b47686 b47687 b47688 b47689 g34 g35 d47609 f47682
                      omega
                    have d47690 : (x 3 3).toNat = 1 := by
                      have r47691 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
                      have b47692 := hb (x 3 3)
                      have b47693 := hb (x 3 11)
                      clear * - r47691 b47692 b47693 d47683
                      omega
                    have d47694 : (x 6 12).toNat = 0 := by
                      have r47695 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47696 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                      have e47697 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                      have b47698 := hb (x 3 3)
                      have b47699 := hb (x 4 2)
                      have b47700 := hb (x 5 13)
                      have b47701 := hb (x 6 12)
                      clear * - r47695 e47696 e47697 b47698 b47699 b47700 b47701 d47690
                      omega
                    have d47702 : (x 5 13).toNat = 0 := by
                      have r47703 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47704 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                      have e47705 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                      have b47706 := hb (x 3 3)
                      have b47707 := hb (x 4 2)
                      have b47708 := hb (x 5 13)
                      have b47709 := hb (x 6 12)
                      clear * - r47703 e47704 e47705 b47706 b47707 b47708 b47709 d47694 d47690
                      omega
                    have d47710 : (x 4 2).toNat = 0 := by
                      have r47711 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47712 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                      have e47713 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                      have b47714 := hb (x 3 3)
                      have b47715 := hb (x 4 2)
                      have b47716 := hb (x 5 13)
                      have b47717 := hb (x 6 12)
                      clear * - r47711 e47712 e47713 b47714 b47715 b47716 b47717 d47694 d47702 d47690
                      omega
                    have d47718 : (x 4 10).toNat = 0 := by
                      have r47719 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
                      have b47720 := hb (x 4 2)
                      have b47721 := hb (x 4 10)
                      clear * - r47719 b47720 b47721 d47710
                      omega
                    have d47722 : (x 3 1 && x 3 11).toNat = 1 := by
                      have r47723 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47724 := hb (x (-1) 5)
                      have b47725 := hb (x 4 10)
                      have b47726 := hb (x 3 1 && x 3 11)
                      have b47727 := hb (x 2 2 && x 2 12)
                      have b47728 := hb (x 1 3 && x 1 13)
                      have b47729 := hb (x 0 4 && x 0 14)
                      clear * - r47723 b47724 b47725 b47726 b47727 b47728 b47729 d47718 g27 g28 d47631 g5
                      omega
                    have d47730 : (x 3 1).toNat = 1 := by
                      have r47731 := hand1 (x 3 1) (x 3 11)
                      have b47732 := hb (x 3 1)
                      have b47733 := hb (x 3 1 && x 3 11)
                      clear * - r47731 b47732 b47733 d47722
                      omega
                    have d47734 : (x 4 14).toNat = 0 := by
                      have r47735 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47736 := hb (x 3 1)
                      have b47737 := hb (x 4 14)
                      clear * - r47735 b47736 b47737 d47730
                      omega
                    have d47738 : (x 4 1 && x 4 14).toNat = 0 := by
                      have r47739 := hand2 (x 4 1) (x 4 14)
                      have b47740 := hb (x 4 14)
                      have b47741 := hb (x 4 1 && x 4 14)
                      clear * - r47739 b47740 b47741 d47734
                      omega
                    have d47742 : (x 3 2).toNat = 1 := by
                      have r47743 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47744 := hb (x 3 2)
                      have b47745 := hb (x 5 13)
                      have b47746 := hb (x 4 1 && x 4 14)
                      clear * - r47743 b47744 b47745 b47746 d47702 d47738
                      omega
                    have d47747 : (x 3 14).toNat = 1 := by
                      have r47748 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                      have b47749 := hb (x 3 2)
                      have b47750 := hb (x 3 14)
                      clear * - r47748 b47749 b47750 d47742
                      omega
                    have d47751 : (x 2 1).toNat = 0 := by
                      have r47752 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47753 := hb (x 2 1)
                      have b47754 := hb (x 3 14)
                      clear * - r47752 b47753 b47754 d47747
                      omega
                    have d47755 : (x 2 1 && x 2 14).toNat = 0 := by
                      have r47756 := hand1 (x 2 1) (x 2 14)
                      have b47757 := hb (x 2 1)
                      have b47758 := hb (x 2 1 && x 2 14)
                      clear * - r47756 b47757 b47758 d47751
                      omega
                    have d47759 : (x 3 13).toNat = 1 := by
                      have r47760 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47761 := hb (x 1 2)
                      have b47762 := hb (x 3 13)
                      have b47763 := hb (x 2 1 && x 2 14)
                      clear * - r47760 b47761 b47762 b47763 d47755 g12
                      omega
                    have d47764 : (x 4 12).toNat = 0 := by
                      have r47765 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47766 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                      have e47767 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                      have b47768 := hb (x 1 3)
                      have b47769 := hb (x 2 2)
                      have b47770 := hb (x 3 13)
                      have b47771 := hb (x 4 12)
                      clear * - r47765 e47766 e47767 b47768 b47769 b47770 b47771 d47759 f47676
                      omega
                    have d47772 : (x 2 2).toNat = 0 := by
                      have r47773 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47774 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                      have e47775 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                      have b47776 := hb (x 1 3)
                      have b47777 := hb (x 2 2)
                      have b47778 := hb (x 3 13)
                      have b47779 := hb (x 4 12)
                      clear * - r47773 e47774 e47775 b47776 b47777 b47778 b47779 d47764 d47759 f47676
                      omega
                    have d47780 : (x 2 10).toNat = 0 := by
                      have r47781 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
                      have b47782 := hb (x 2 2)
                      have b47783 := hb (x 2 10)
                      clear * - r47781 b47782 b47783 d47772
                      omega
                    have r47784 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := by have q := hcount 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47785 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47786 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47787 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                    have e47788 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                    have e47789 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                    have e47790 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                    have e47791 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                    have e47792 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                    have r47793 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47794 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                    have e47795 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                    have r47796 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e47797 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
                    have e47798 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
                    have r47799 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := by have q := hcov5 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47800 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47801 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47802 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47803 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47804 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have r47805 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
                    have r47806 := hand2 (x (-2) 4) (x (-2) 8)
                    have r47807 := hand2 (x (-3) 5) (x (-3) 9)
                    have r47808 := hand1 (x (-4) 6) (x (-4) 10)
                    have r47809 := hand1 (x (-5) 7) (x (-5) 11)
                    have r47810 := hand1 (x (-6) 8) (x (-6) 12)
                    have r47811 := hand1 (x (-7) 9) (x (-7) 13)
                    have r47812 := hand2 (x (-2) 3) (x (-2) 8)
                    have r47813 := hand2 (x (-3) 4) (x (-3) 9)
                    have r47814 := hand1 (x (-4) 5) (x (-4) 10)
                    have r47815 := hand1 (x (-5) 6) (x (-5) 11)
                    have r47816 := hand1 (x (-6) 7) (x (-6) 12)
                    have r47817 := hand1 (x (-7) 8) (x (-7) 13)
                    have r47818 := hand1 (x (-8) 9) (x (-8) 14)
                    have r47819 := hand1 (x (-4) 2) (x (-4) 12)
                    have r47820 := hand1 (x (-5) 3) (x (-5) 13)
                    have r47821 := hand1 (x (-6) 4) (x (-6) 14)
                    have r47822 := hand2 (x (-2) 2) (x (-2) 12)
                    have r47823 := hand2 (x (-3) 3) (x (-3) 13)
                    have r47824 := hand1 (x (-2) 4) (x (-2) 14)
                    have r47825 := hand1 (x (-2) 3) (x (-2) 14)
                    have r47826 := hand2 (x (-12) 1) (x (-12) 14)
                    linarith only [r47784, r47785, r47786, e47787, e47788, e47789, e47790, e47791, e47792, r47793, e47794, e47795, r47796, e47797, e47798, r47799, r47800, r47801, r47802, r47803, r47804, r47805, r47806, r47807, r47808, r47809, r47810, r47811, r47812, r47813, r47814, r47815, r47816, r47817, r47818, r47819, r47820, r47821, r47822, r47823, r47824, r47825, r47826, g1, g3, f47670, g4, g8, g9, f47648, f47660, g13, d47677, g15, d47780, d47643, g16, d47639, d47671, g22, g23, g24, d47665, d47655, g25, d47651, g32]
                  · have f47908 : (x (-1) 4).toNat = 1 := by rw [h47681]; rfl
                    have d47909 : (x (-1) 12).toNat = 1 := by
                      have r47910 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                      have b47911 := hb (x (-1) 4)
                      have b47912 := hb (x (-1) 12)
                      clear * - r47910 b47911 b47912 f47908
                      omega
                    have d47913 : (x (-2) 13).toNat = 0 := by
                      have r47914 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47915 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e47916 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have b47917 := hb (x (-4) 3)
                      have b47918 := hb (x (-3) 2)
                      have b47919 := hb (x (-2) 13)
                      have b47920 := hb (x (-1) 12)
                      clear * - r47914 e47915 e47916 b47917 b47918 b47919 b47920 d47909
                      omega
                    have d47921 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
                      have r47922 := hand2 (x (-2) 2) (x (-2) 13)
                      have b47923 := hb (x (-2) 13)
                      have b47924 := hb (x (-2) 2 && x (-2) 13)
                      clear * - r47922 b47923 b47924 d47913
                      omega
                    have d47925 : (x (-3) 2).toNat = 0 := by
                      have r47926 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47927 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                      have e47928 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                      have b47929 := hb (x (-4) 3)
                      have b47930 := hb (x (-3) 2)
                      have b47931 := hb (x (-2) 13)
                      have b47932 := hb (x (-1) 12)
                      clear * - r47926 e47927 e47928 b47929 b47930 b47931 b47932 d47909 d47913
                      omega
                    have d47933 : (x (-2) 1 && x (-2) 14).toNat = 1 := by
                      have r47934 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47935 := hb (x (-3) 2)
                      have b47936 := hb (x (-1) 13)
                      have b47937 := hb (x (-2) 1 && x (-2) 14)
                      clear * - r47934 b47935 b47936 b47937 g7 d47925
                      omega
                    have d47938 : (x (-2) 14).toNat = 1 := by
                      have r47939 := hand2 (x (-2) 1) (x (-2) 14)
                      have b47940 := hb (x (-2) 14)
                      have b47941 := hb (x (-2) 1 && x (-2) 14)
                      clear * - r47939 b47940 b47941 d47933
                      omega
                    have d47942 : (x (-3) 1).toNat = 0 := by
                      have r47943 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47944 := hb (x (-3) 1)
                      have b47945 := hb (x (-2) 14)
                      clear * - r47943 b47944 b47945 d47938
                      omega
                    have d47946 : (x (-3) 13).toNat = 0 := by
                      have r47947 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                      have b47948 := hb (x (-3) 1)
                      have b47949 := hb (x (-3) 13)
                      clear * - r47947 b47948 b47949 d47942
                      omega
                    have d47950 : (x (-3) 3 && x (-3) 14).toNat = 1 := by
                      have r47951 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47952 := hb (x (-4) 4)
                      have b47953 := hb (x 0 11)
                      have b47954 := hb (x (-1) 1 && x (-1) 12)
                      have b47955 := hb (x (-2) 2 && x (-2) 13)
                      have b47956 := hb (x (-3) 3 && x (-3) 14)
                      clear * - r47951 b47952 b47953 b47954 b47955 b47956 d47617 g31 d47921 g2
                      omega
                    have d47957 : (x (-3) 14).toNat = 1 := by
                      have r47958 := hand2 (x (-3) 3) (x (-3) 14)
                      have b47959 := hb (x (-3) 14)
                      have b47960 := hb (x (-3) 3 && x (-3) 14)
                      clear * - r47958 b47959 b47960 d47950
                      omega
                    have d47961 : (x (-4) 1).toNat = 0 := by
                      have r47962 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47963 := hb (x (-4) 1)
                      have b47964 := hb (x (-3) 14)
                      clear * - r47962 b47963 b47964 d47957
                      omega
                    have d47965 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
                      have r47966 := hand1 (x (-4) 1) (x (-4) 14)
                      have b47967 := hb (x (-4) 1)
                      have b47968 := hb (x (-4) 1 && x (-4) 14)
                      clear * - r47966 b47967 b47968 d47961
                      omega
                    have d47969 : (x (-5) 2).toNat = 1 := by
                      have r47970 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47971 := hb (x (-5) 2)
                      have b47972 := hb (x (-3) 13)
                      have b47973 := hb (x (-4) 1 && x (-4) 14)
                      clear * - r47970 b47971 b47972 b47973 d47946 d47965
                      omega
                    have d47974 : (x (-3) 12).toNat = 0 := by
                      have r47975 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47976 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                      have e47977 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                      have b47978 := hb (x (-6) 3)
                      have b47979 := hb (x (-5) 2)
                      have b47980 := hb (x (-4) 13)
                      have b47981 := hb (x (-3) 12)
                      clear * - r47975 e47976 e47977 b47978 b47979 b47980 b47981 d47969
                      omega
                    have d47982 : (x (-3) 4).toNat = 0 := by
                      have r47983 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
                      have b47984 := hb (x (-3) 4)
                      have b47985 := hb (x (-3) 12)
                      clear * - r47983 b47984 b47985 d47974
                      omega
                    have d47986 : (x (-2) 3 && x (-2) 14).toNat = 1 := by
                      have r47987 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b47988 := hb (x (-3) 4)
                      have b47989 := hb (x 1 11)
                      have b47990 := hb (x 0 1 && x 0 12)
                      have b47991 := hb (x (-1) 2 && x (-1) 13)
                      have b47992 := hb (x (-2) 3 && x (-2) 14)
                      clear * - r47987 b47988 b47989 b47990 b47991 b47992 d47677 d47651 g32 d47982
                      omega
                    have d47993 : (x (-2) 3).toNat = 1 := by
                      have r47994 := hand1 (x (-2) 3) (x (-2) 14)
                      have b47995 := hb (x (-2) 3)
                      have b47996 := hb (x (-2) 3 && x (-2) 14)
                      clear * - r47994 b47995 b47996 d47986
                      omega
                    have d47997 : (x 1 12).toNat = 0 := by
                      have r47998 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e47999 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                      have e48000 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                      have b48001 := hb (x (-2) 3)
                      have b48002 := hb (x (-1) 2)
                      have b48003 := hb (x 0 13)
                      have b48004 := hb (x 1 12)
                      clear * - r47998 e47999 e48000 b48001 b48002 b48003 b48004 f47670 d47993
                      omega
                    have d48005 : (x 0 13).toNat = 0 := by
                      have r48006 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e48007 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                      have e48008 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                      have b48009 := hb (x (-2) 3)
                      have b48010 := hb (x (-1) 2)
                      have b48011 := hb (x 0 13)
                      have b48012 := hb (x 1 12)
                      clear * - r48006 e48007 e48008 b48009 b48010 b48011 b48012 d47997 f47670 d47993
                      omega
                    have d48013 : (x (-2) 2).toNat = 1 := by
                      have r48014 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b48015 := hb (x (-2) 2)
                      have b48016 := hb (x 0 13)
                      have b48017 := hb (x (-1) 1 && x (-1) 14)
                      clear * - r48014 b48015 b48016 b48017 d48005 g36
                      omega
                    have d48018 : (x (-3) 3).toNat = 0 := by
                      have r48019 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e48020 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                      have e48021 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                      have b48022 := hb (x (-3) 3)
                      have b48023 := hb (x (-2) 2)
                      have b48024 := hb (x (-1) 13)
                      have b48025 := hb (x 0 12)
                      clear * - r48019 e48020 e48021 b48022 b48023 b48024 b48025 f47650 g7 d48013
                      omega
                    have r48026 := hand1 (x (-3) 3) (x (-3) 14)
                    have b48027 := hb (x (-3) 3)
                    have b48028 := hb (x (-3) 3 && x (-3) 14)
                    linarith only [r48026, b48027, b48028, d47950, d48018]
                · have f48029 : (x 1 3).toNat = 1 := by rw [h47675]; rfl
                  have d48030 : (x 4 12).toNat = 0 := by
                    have r48031 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48032 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e48033 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b48034 := hb (x 1 3)
                    have b48035 := hb (x 2 2)
                    have b48036 := hb (x 3 13)
                    have b48037 := hb (x 4 12)
                    clear * - r48031 e48032 e48033 b48034 b48035 b48036 b48037 f48029
                    omega
                  have d48038 : (x 4 1 && x 4 12).toNat = 0 := by
                    have r48039 := hand2 (x 4 1) (x 4 12)
                    have b48040 := hb (x 4 12)
                    have b48041 := hb (x 4 1 && x 4 12)
                    clear * - r48039 b48040 b48041 d48030
                    omega
                  have d48042 : (x 4 2 && x 4 12).toNat = 0 := by
                    have r48043 := hand2 (x 4 2) (x 4 12)
                    have b48044 := hb (x 4 12)
                    have b48045 := hb (x 4 2 && x 4 12)
                    clear * - r48043 b48044 b48045 d48030
                    omega
                  have d48046 : (x 3 13).toNat = 0 := by
                    have r48047 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48048 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e48049 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b48050 := hb (x 1 3)
                    have b48051 := hb (x 2 2)
                    have b48052 := hb (x 3 13)
                    have b48053 := hb (x 4 12)
                    clear * - r48047 e48048 e48049 b48050 b48051 b48052 b48053 d48030 f48029
                    omega
                  have d48054 : (x 3 2 && x 3 13).toNat = 0 := by
                    have r48055 := hand2 (x 3 2) (x 3 13)
                    have b48056 := hb (x 3 13)
                    have b48057 := hb (x 3 2 && x 3 13)
                    clear * - r48055 b48056 b48057 d48046
                    omega
                  have d48058 : (x 3 3 && x 3 13).toNat = 0 := by
                    have r48059 := hand2 (x 3 3) (x 3 13)
                    have b48060 := hb (x 3 13)
                    have b48061 := hb (x 3 3 && x 3 13)
                    clear * - r48059 b48060 b48061 d48046
                    omega
                  have d48062 : (x 2 1 && x 2 14).toNat = 1 := by
                    have r48063 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b48064 := hb (x 1 2)
                    have b48065 := hb (x 3 13)
                    have b48066 := hb (x 2 1 && x 2 14)
                    clear * - r48063 b48064 b48065 b48066 d48046 g12
                    omega
                  have d48067 : (x 2 1).toNat = 1 := by
                    have r48068 := hand1 (x 2 1) (x 2 14)
                    have b48069 := hb (x 2 1)
                    have b48070 := hb (x 2 1 && x 2 14)
                    clear * - r48068 b48069 b48070 d48062
                    omega
                  have d48071 : (x 3 14).toNat = 0 := by
                    have r48072 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b48073 := hb (x 2 1)
                    have b48074 := hb (x 3 14)
                    clear * - r48072 b48073 b48074 d48067
                    omega
                  have d48075 : (x 3 1 && x 3 14).toNat = 0 := by
                    have r48076 := hand2 (x 3 1) (x 3 14)
                    have b48077 := hb (x 3 14)
                    have b48078 := hb (x 3 1 && x 3 14)
                    clear * - r48076 b48077 b48078 d48071
                    omega
                  have d48079 : (x 3 2).toNat = 0 := by
                    have r48080 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
                    have b48081 := hb (x 3 2)
                    have b48082 := hb (x 3 14)
                    clear * - r48080 b48081 b48082 d48071
                    omega
                  have d48083 : (x 3 2 && x 3 12).toNat = 0 := by
                    have r48084 := hand1 (x 3 2) (x 3 12)
                    have b48085 := hb (x 3 2)
                    have b48086 := hb (x 3 2 && x 3 12)
                    clear * - r48084 b48085 b48086 d48079
                    omega
                  have d48087 : (x 2 2).toNat = 0 := by
                    have r48088 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48089 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                    have e48090 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                    have b48091 := hb (x 1 3)
                    have b48092 := hb (x 2 2)
                    have b48093 := hb (x 3 13)
                    have b48094 := hb (x 4 12)
                    clear * - r48088 e48089 e48090 b48091 b48092 b48093 b48094 d48030 d48046 f48029
                    omega
                  have d48095 : (x 4 13).toNat = 1 := by
                    have r48096 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b48097 := hb (x 2 2)
                    have b48098 := hb (x 4 13)
                    have b48099 := hb (x 3 1 && x 3 14)
                    clear * - r48096 b48097 b48098 b48099 d48075 d48087
                    omega
                  have d48100 : (x 4 1).toNat = 1 := by
                    have r48101 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
                    have b48102 := hb (x 4 1)
                    have b48103 := hb (x 4 13)
                    clear * - r48101 b48102 b48103 d48095
                    omega
                  have d48104 : (x 5 14).toNat = 0 := by
                    have r48105 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b48106 := hb (x 4 1)
                    have b48107 := hb (x 5 14)
                    clear * - r48105 b48106 b48107 d48100
                    omega
                  have d48108 : (x 5 1 && x 5 14).toNat = 0 := by
                    have r48109 := hand2 (x 5 1) (x 5 14)
                    have b48110 := hb (x 5 14)
                    have b48111 := hb (x 5 1 && x 5 14)
                    clear * - r48109 b48110 b48111 d48104
                    omega
                  have d48112 : (x 5 2).toNat = 0 := by
                    have r48113 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                    have b48114 := hb (x 5 2)
                    have b48115 := hb (x 5 14)
                    clear * - r48113 b48114 b48115 d48104
                    omega
                  have d48116 : (x 5 10).toNat = 0 := by
                    have r48117 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
                    have b48118 := hb (x 5 2)
                    have b48119 := hb (x 5 10)
                    clear * - r48117 b48118 b48119 d48112
                    omega
                  have d48120 : (x 5 12).toNat = 0 := by
                    have r48121 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48122 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                    have e48123 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                    have b48124 := hb (x 2 3)
                    have b48125 := hb (x 3 2)
                    have b48126 := hb (x 4 13)
                    have b48127 := hb (x 5 12)
                    clear * - r48121 e48122 e48123 b48124 b48125 b48126 b48127 d48095 d48079
                    omega
                  have d48128 : (x 2 3).toNat = 0 := by
                    have r48129 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48130 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                    have e48131 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                    have b48132 := hb (x 2 3)
                    have b48133 := hb (x 3 2)
                    have b48134 := hb (x 4 13)
                    have b48135 := hb (x 5 12)
                    clear * - r48129 e48130 e48131 b48132 b48133 b48134 b48135 d48120 d48095 d48079
                    omega
                  have d48136 : (x 2 3 && x 2 14).toNat = 0 := by
                    have r48137 := hand1 (x 2 3) (x 2 14)
                    have b48138 := hb (x 2 3)
                    have b48139 := hb (x 2 3 && x 2 14)
                    clear * - r48137 b48138 b48139 d48128
                    omega
                  have d48140 : (x 2 3 && x 2 13).toNat = 0 := by
                    have r48141 := hand1 (x 2 3) (x 2 13)
                    have b48142 := hb (x 2 3)
                    have b48143 := hb (x 2 3 && x 2 13)
                    clear * - r48141 b48142 b48143 d48128
                    omega
                  have d48144 : (x 4 1 && x 4 11).toNat = 1 := by
                    have r48145 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b48146 := hb (x 0 5)
                    have b48147 := hb (x 5 10)
                    have b48148 := hb (x 4 1 && x 4 11)
                    have b48149 := hb (x 3 2 && x 3 12)
                    have b48150 := hb (x 2 3 && x 2 13)
                    have b48151 := hb (x 1 4 && x 1 14)
                    clear * - r48145 b48146 b48147 b48148 b48149 b48150 b48151 d48116 d48083 d48140 g29 f47636
                    omega
                  have d48152 : (x 4 11).toNat = 1 := by
                    have r48153 := hand2 (x 4 1) (x 4 11)
                    have b48154 := hb (x 4 11)
                    have b48155 := hb (x 4 1 && x 4 11)
                    clear * - r48153 b48154 b48155 d48144
                    omega
                  have d48156 : (x 4 3).toNat = 1 := by
                    have r48157 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
                    have b48158 := hb (x 4 3)
                    have b48159 := hb (x 4 11)
                    clear * - r48157 b48158 b48159 d48152
                    omega
                  have d48160 : (x 7 12).toNat = 0 := by
                    have r48161 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48162 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                    have e48163 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                    have b48164 := hb (x 4 3)
                    have b48165 := hb (x 5 2)
                    have b48166 := hb (x 6 13)
                    have b48167 := hb (x 7 12)
                    clear * - r48161 e48162 e48163 b48164 b48165 b48166 b48167 d48112 d48156
                    omega
                  have d48168 : (x 6 13).toNat = 0 := by
                    have r48169 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48170 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
                    have e48171 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
                    have b48172 := hb (x 4 3)
                    have b48173 := hb (x 5 2)
                    have b48174 := hb (x 6 13)
                    have b48175 := hb (x 7 12)
                    clear * - r48169 e48170 e48171 b48172 b48173 b48174 b48175 d48160 d48112 d48156
                    omega
                  have d48176 : (x 4 2).toNat = 1 := by
                    have r48177 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b48178 := hb (x 4 2)
                    have b48179 := hb (x 6 13)
                    have b48180 := hb (x 5 1 && x 5 14)
                    clear * - r48177 b48178 b48179 b48180 d48168 d48108
                    omega
                  have d48181 : (x 6 12).toNat = 0 := by
                    have r48182 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48183 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                    have e48184 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                    have b48185 := hb (x 3 3)
                    have b48186 := hb (x 4 2)
                    have b48187 := hb (x 5 13)
                    have b48188 := hb (x 6 12)
                    clear * - r48182 e48183 e48184 b48185 b48186 b48187 b48188 d48176
                    omega
                  have d48189 : (x 5 13).toNat = 0 := by
                    have r48190 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48191 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                    have e48192 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                    have b48193 := hb (x 3 3)
                    have b48194 := hb (x 4 2)
                    have b48195 := hb (x 5 13)
                    have b48196 := hb (x 6 12)
                    clear * - r48190 e48191 e48192 b48193 b48194 b48195 b48196 d48181 d48176
                    omega
                  have d48197 : (x 3 3).toNat = 0 := by
                    have r48198 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48199 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                    have e48200 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                    have b48201 := hb (x 3 3)
                    have b48202 := hb (x 4 2)
                    have b48203 := hb (x 5 13)
                    have b48204 := hb (x 6 12)
                    clear * - r48198 e48199 e48200 b48201 b48202 b48203 b48204 d48181 d48189 d48176
                    omega
                  have d48205 : (x 3 11).toNat = 0 := by
                    have r48206 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
                    have b48207 := hb (x 3 3)
                    have b48208 := hb (x 3 11)
                    clear * - r48206 b48207 b48208 d48197
                    omega
                  have d48209 : (x (-1) 4).toNat = 1 := by
                    have r48210 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b48211 := hb (x (-1) 4)
                    have b48212 := hb (x 3 11)
                    have b48213 := hb (x 2 1 && x 2 12)
                    have b48214 := hb (x 1 2 && x 1 13)
                    have b48215 := hb (x 0 3 && x 0 14)
                    clear * - r48210 b48211 b48212 b48213 b48214 b48215 d48205 g34 g35 d47609
                    omega
                  have d48216 : (x (-1) 12).toNat = 1 := by
                    have r48217 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                    have b48218 := hb (x (-1) 4)
                    have b48219 := hb (x (-1) 12)
                    clear * - r48217 b48218 b48219 d48209
                    omega
                  have d48220 : (x (-2) 13).toNat = 0 := by
                    have r48221 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48222 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                    have e48223 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                    have b48224 := hb (x (-4) 3)
                    have b48225 := hb (x (-3) 2)
                    have b48226 := hb (x (-2) 13)
                    have b48227 := hb (x (-1) 12)
                    clear * - r48221 e48222 e48223 b48224 b48225 b48226 b48227 d48216
                    omega
                  have d48228 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
                    have r48229 := hand2 (x (-2) 2) (x (-2) 13)
                    have b48230 := hb (x (-2) 13)
                    have b48231 := hb (x (-2) 2 && x (-2) 13)
                    clear * - r48229 b48230 b48231 d48220
                    omega
                  have d48232 : (x (-3) 3 && x (-3) 14).toNat = 1 := by
                    have r48233 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b48234 := hb (x (-4) 4)
                    have b48235 := hb (x 0 11)
                    have b48236 := hb (x (-1) 1 && x (-1) 12)
                    have b48237 := hb (x (-2) 2 && x (-2) 13)
                    have b48238 := hb (x (-3) 3 && x (-3) 14)
                    clear * - r48233 b48234 b48235 b48236 b48237 b48238 d47617 g31 d48228 g2
                    omega
                  have d48239 : (x (-3) 3).toNat = 1 := by
                    have r48240 := hand1 (x (-3) 3) (x (-3) 14)
                    have b48241 := hb (x (-3) 3)
                    have b48242 := hb (x (-3) 3 && x (-3) 14)
                    clear * - r48240 b48241 b48242 d48232
                    omega
                  have d48243 : (x (-2) 2).toNat = 0 := by
                    have r48244 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48245 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                    have e48246 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                    have b48247 := hb (x (-3) 3)
                    have b48248 := hb (x (-2) 2)
                    have b48249 := hb (x (-1) 13)
                    have b48250 := hb (x 0 12)
                    clear * - r48244 e48245 e48246 b48247 b48248 b48249 b48250 f47650 g7 d48239
                    omega
                  have d48251 : (x 0 13).toNat = 1 := by
                    have r48252 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b48253 := hb (x (-2) 2)
                    have b48254 := hb (x 0 13)
                    have b48255 := hb (x (-1) 1 && x (-1) 14)
                    clear * - r48252 b48253 b48254 b48255 g36 d48243
                    omega
                  have d48256 : (x 1 12).toNat = 0 := by
                    have r48257 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48258 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                    have e48259 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                    have b48260 := hb (x (-2) 3)
                    have b48261 := hb (x (-1) 2)
                    have b48262 := hb (x 0 13)
                    have b48263 := hb (x 1 12)
                    clear * - r48257 e48258 e48259 b48260 b48261 b48262 b48263 d48251 f47670
                    omega
                  have d48264 : (x 1 4).toNat = 0 := by
                    have r48265 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
                    have b48266 := hb (x 1 4)
                    have b48267 := hb (x 1 12)
                    clear * - r48265 b48266 b48267 d48256
                    omega
                  have d48268 : (x 5 11).toNat = 1 := by
                    have r48269 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b48270 := hb (x 1 4)
                    have b48271 := hb (x 5 11)
                    have b48272 := hb (x 4 1 && x 4 12)
                    have b48273 := hb (x 3 2 && x 3 13)
                    have b48274 := hb (x 2 3 && x 2 14)
                    clear * - r48269 b48270 b48271 b48272 b48273 b48274 d48038 d48054 d48136 d48264
                    omega
                  have d48275 : (x 5 3).toNat = 1 := by
                    have r48276 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
                    have b48277 := hb (x 5 3)
                    have b48278 := hb (x 5 11)
                    clear * - r48276 b48277 b48278 d48268
                    omega
                  have d48279 : (x 8 12).toNat = 0 := by
                    have r48280 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48281 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                    have e48282 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                    have b48283 := hb (x 5 3)
                    have b48284 := hb (x 6 2)
                    have b48285 := hb (x 7 13)
                    have b48286 := hb (x 8 12)
                    clear * - r48280 e48281 e48282 b48283 b48284 b48285 b48286 d48275
                    omega
                  have d48287 : (x 7 13).toNat = 0 := by
                    have r48288 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e48289 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                    have e48290 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                    have b48291 := hb (x 5 3)
                    have b48292 := hb (x 6 2)
                    have b48293 := hb (x 7 13)
                    have b48294 := hb (x 8 12)
                    clear * - r48288 e48289 e48290 b48291 b48292 b48293 b48294 d48279 d48275
                    omega
                  have d48295 : (x 6 1 && x 6 14).toNat = 1 := by
                    have r48296 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b48297 := hb (x 5 2)
                    have b48298 := hb (x 7 13)
                    have b48299 := hb (x 6 1 && x 6 14)
                    clear * - r48296 b48297 b48298 b48299 d48287 d48112
                    omega
                  have d48300 : (x 6 14).toNat = 1 := by
                    have r48301 := hand2 (x 6 1) (x 6 14)
                    have b48302 := hb (x 6 14)
                    have b48303 := hb (x 6 1 && x 6 14)
                    clear * - r48301 b48302 b48303 d48295
                    omega
                  have d48304 : (x 5 1).toNat = 0 := by
                    have r48305 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b48306 := hb (x 5 1)
                    have b48307 := hb (x 6 14)
                    clear * - r48305 b48306 b48307 d48300
                    omega
                  have d48308 : (x 5 1 && x 5 11).toNat = 0 := by
                    have r48309 := hand1 (x 5 1) (x 5 11)
                    have b48310 := hb (x 5 1)
                    have b48311 := hb (x 5 1 && x 5 11)
                    clear * - r48309 b48310 b48311 d48304
                    omega
                  have d48312 : (x 6 10).toNat = 1 := by
                    have r48313 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b48314 := hb (x 1 5)
                    have b48315 := hb (x 6 10)
                    have b48316 := hb (x 5 1 && x 5 11)
                    have b48317 := hb (x 4 2 && x 4 12)
                    have b48318 := hb (x 3 3 && x 3 13)
                    have b48319 := hb (x 2 4 && x 2 14)
                    clear * - r48313 b48314 b48315 b48316 b48317 b48318 b48319 d48308 d48042 d48058 g30 g13
                    omega
                  have d48320 : (x 6 2).toNat = 1 := by
                    have r48321 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
                    have b48322 := hb (x 6 2)
                    have b48323 := hb (x 6 10)
                    clear * - r48321 b48322 b48323 d48312
                    omega
                  have r48324 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48325 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                  have e48326 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                  have b48327 := hb (x 5 3)
                  have b48328 := hb (x 6 2)
                  have b48329 := hb (x 7 13)
                  have b48330 := hb (x 8 12)
                  linarith only [r48324, e48325, e48326, b48327, b48328, b48329, b48330, d48279, d48287, d48320, d48275]
              · have f48331 : (x (-1) 2).toNat = 1 := by rw [h47669]; rfl
                have d48332 : (x (-1) 14).toNat = 1 := by
                  have r48333 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
                  have b48334 := hb (x (-1) 2)
                  have b48335 := hb (x (-1) 14)
                  clear * - r48333 b48334 b48335 f48331
                  omega
                have d48336 : (x (-2) 1).toNat = 0 := by
                  have r48337 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b48338 := hb (x (-2) 1)
                  have b48339 := hb (x (-1) 14)
                  clear * - r48337 b48338 b48339 d48332
                  omega
                have d48340 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                  have r48341 := hand1 (x (-2) 1) (x (-2) 14)
                  have b48342 := hb (x (-2) 1)
                  have b48343 := hb (x (-2) 1 && x (-2) 14)
                  clear * - r48341 b48342 b48343 d48336
                  omega
                have d48344 : (x (-2) 13).toNat = 0 := by
                  have r48345 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                  have b48346 := hb (x (-2) 1)
                  have b48347 := hb (x (-2) 13)
                  clear * - r48345 b48346 b48347 d48336
                  omega
                have d48348 : (x (-3) 2).toNat = 1 := by
                  have r48349 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b48350 := hb (x (-3) 2)
                  have b48351 := hb (x (-1) 13)
                  have b48352 := hb (x (-2) 1 && x (-2) 14)
                  clear * - r48349 b48350 b48351 b48352 g7 d48340
                  omega
                have d48353 : (x (-3) 14).toNat = 1 := by
                  have r48354 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                  have b48355 := hb (x (-3) 2)
                  have b48356 := hb (x (-3) 14)
                  clear * - r48354 b48355 b48356 d48348
                  omega
                have d48357 : (x (-4) 1).toNat = 0 := by
                  have r48358 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b48359 := hb (x (-4) 1)
                  have b48360 := hb (x (-3) 14)
                  clear * - r48358 b48359 b48360 d48353
                  omega
                have d48361 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
                  have r48362 := hand1 (x (-4) 1) (x (-4) 14)
                  have b48363 := hb (x (-4) 1)
                  have b48364 := hb (x (-4) 1 && x (-4) 14)
                  clear * - r48362 b48363 b48364 d48357
                  omega
                have d48365 : (x (-4) 13).toNat = 0 := by
                  have r48366 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
                  have b48367 := hb (x (-4) 1)
                  have b48368 := hb (x (-4) 13)
                  clear * - r48366 b48367 b48368 d48357
                  omega
                have d48369 : (x 1 12).toNat = 0 := by
                  have r48370 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48371 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                  have e48372 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                  have b48373 := hb (x (-2) 3)
                  have b48374 := hb (x (-1) 2)
                  have b48375 := hb (x 0 13)
                  have b48376 := hb (x 1 12)
                  clear * - r48370 e48371 e48372 b48373 b48374 b48375 b48376 f48331
                  omega
                have d48377 : (x 0 13).toNat = 0 := by
                  have r48378 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48379 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                  have e48380 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                  have b48381 := hb (x (-2) 3)
                  have b48382 := hb (x (-1) 2)
                  have b48383 := hb (x 0 13)
                  have b48384 := hb (x 1 12)
                  clear * - r48378 e48379 e48380 b48381 b48382 b48383 b48384 d48369 f48331
                  omega
                have d48385 : (x 0 2 && x 0 13).toNat = 0 := by
                  have r48386 := hand2 (x 0 2) (x 0 13)
                  have b48387 := hb (x 0 13)
                  have b48388 := hb (x 0 2 && x 0 13)
                  clear * - r48386 b48387 b48388 d48377
                  omega
                have d48389 : (x (-2) 2).toNat = 1 := by
                  have r48390 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b48391 := hb (x (-2) 2)
                  have b48392 := hb (x 0 13)
                  have b48393 := hb (x (-1) 1 && x (-1) 14)
                  clear * - r48390 b48391 b48392 b48393 d48377 g36
                  omega
                have d48394 : (x (-2) 14).toNat = 1 := by
                  have r48395 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
                  have b48396 := hb (x (-2) 2)
                  have b48397 := hb (x (-2) 14)
                  clear * - r48395 b48396 b48397 d48389
                  omega
                have d48398 : (x (-3) 1).toNat = 0 := by
                  have r48399 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b48400 := hb (x (-3) 1)
                  have b48401 := hb (x (-2) 14)
                  clear * - r48399 b48400 b48401 d48394
                  omega
                have d48402 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
                  have r48403 := hand1 (x (-3) 1) (x (-3) 14)
                  have b48404 := hb (x (-3) 1)
                  have b48405 := hb (x (-3) 1 && x (-3) 14)
                  clear * - r48403 b48404 b48405 d48398
                  omega
                have d48406 : (x (-4) 2).toNat = 1 := by
                  have r48407 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b48408 := hb (x (-4) 2)
                  have b48409 := hb (x (-2) 13)
                  have b48410 := hb (x (-3) 1 && x (-3) 14)
                  clear * - r48407 b48408 b48409 b48410 d48344 d48402
                  omega
                have d48411 : (x (-3) 13).toNat = 0 := by
                  have r48412 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                  have b48413 := hb (x (-3) 1)
                  have b48414 := hb (x (-3) 13)
                  clear * - r48412 b48413 b48414 d48398
                  omega
                have d48415 : (x (-5) 2).toNat = 1 := by
                  have r48416 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b48417 := hb (x (-5) 2)
                  have b48418 := hb (x (-3) 13)
                  have b48419 := hb (x (-4) 1 && x (-4) 14)
                  clear * - r48416 b48417 b48418 b48419 d48411 d48361
                  omega
                have d48420 : (x (-2) 3).toNat = 0 := by
                  have r48421 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48422 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                  have e48423 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                  have b48424 := hb (x (-2) 3)
                  have b48425 := hb (x (-1) 2)
                  have b48426 := hb (x 0 13)
                  have b48427 := hb (x 1 12)
                  clear * - r48421 e48422 e48423 b48424 b48425 b48426 b48427 d48369 d48377 f48331
                  omega
                have d48428 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
                  have r48429 := hand1 (x (-2) 3) (x (-2) 14)
                  have b48430 := hb (x (-2) 3)
                  have b48431 := hb (x (-2) 3 && x (-2) 14)
                  clear * - r48429 b48430 b48431 d48420
                  omega
                have d48432 : (x (-1) 12).toNat = 0 := by
                  have r48433 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48434 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e48435 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b48436 := hb (x (-4) 3)
                  have b48437 := hb (x (-3) 2)
                  have b48438 := hb (x (-2) 13)
                  have b48439 := hb (x (-1) 12)
                  clear * - r48433 e48434 e48435 b48436 b48437 b48438 b48439 d48344 d48348
                  omega
                have d48440 : (x (-1) 4).toNat = 0 := by
                  have r48441 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                  have b48442 := hb (x (-1) 4)
                  have b48443 := hb (x (-1) 12)
                  clear * - r48441 b48442 b48443 d48432
                  omega
                have d48444 : (x (-2) 12).toNat = 0 := by
                  have r48445 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48446 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                  have e48447 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                  have b48448 := hb (x (-5) 3)
                  have b48449 := hb (x (-4) 2)
                  have b48450 := hb (x (-3) 13)
                  have b48451 := hb (x (-2) 12)
                  clear * - r48445 e48446 e48447 b48448 b48449 b48450 b48451 d48411 d48406
                  omega
                have d48452 : (x (-2) 4).toNat = 0 := by
                  have r48453 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
                  have b48454 := hb (x (-2) 4)
                  have b48455 := hb (x (-2) 12)
                  clear * - r48453 b48454 b48455 d48444
                  omega
                have d48456 : (x (-3) 12).toNat = 0 := by
                  have r48457 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48458 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                  have e48459 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                  have b48460 := hb (x (-6) 3)
                  have b48461 := hb (x (-5) 2)
                  have b48462 := hb (x (-4) 13)
                  have b48463 := hb (x (-3) 12)
                  clear * - r48457 e48458 e48459 b48460 b48461 b48462 b48463 d48365 d48415
                  omega
                have d48464 : (x (-3) 4).toNat = 0 := by
                  have r48465 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
                  have b48466 := hb (x (-3) 4)
                  have b48467 := hb (x (-3) 12)
                  clear * - r48465 b48466 b48467 d48456
                  omega
                have d48468 : (x 3 11).toNat = 1 := by
                  have r48469 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b48470 := hb (x (-1) 4)
                  have b48471 := hb (x 3 11)
                  have b48472 := hb (x 2 1 && x 2 12)
                  have b48473 := hb (x 1 2 && x 1 13)
                  have b48474 := hb (x 0 3 && x 0 14)
                  clear * - r48469 b48470 b48471 b48472 b48473 b48474 g34 g35 d47609 d48440
                  omega
                have d48475 : (x 3 3).toNat = 1 := by
                  have r48476 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
                  have b48477 := hb (x 3 3)
                  have b48478 := hb (x 3 11)
                  clear * - r48476 b48477 b48478 d48468
                  omega
                have d48479 : (x 6 12).toNat = 0 := by
                  have r48480 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48481 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                  have e48482 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                  have b48483 := hb (x 3 3)
                  have b48484 := hb (x 4 2)
                  have b48485 := hb (x 5 13)
                  have b48486 := hb (x 6 12)
                  clear * - r48480 e48481 e48482 b48483 b48484 b48485 b48486 d48475
                  omega
                have d48487 : (x 5 13).toNat = 0 := by
                  have r48488 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48489 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                  have e48490 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                  have b48491 := hb (x 3 3)
                  have b48492 := hb (x 4 2)
                  have b48493 := hb (x 5 13)
                  have b48494 := hb (x 6 12)
                  clear * - r48488 e48489 e48490 b48491 b48492 b48493 b48494 d48479 d48475
                  omega
                have d48495 : (x 2 11).toNat = 1 := by
                  have r48496 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b48497 := hb (x (-2) 4)
                  have b48498 := hb (x 2 11)
                  have b48499 := hb (x 1 1 && x 1 12)
                  have b48500 := hb (x 0 2 && x 0 13)
                  have b48501 := hb (x (-1) 3 && x (-1) 14)
                  clear * - r48496 b48497 b48498 b48499 b48500 b48501 d47661 d48385 g33 d48452
                  omega
                have d48502 : (x 2 3).toNat = 1 := by
                  have r48503 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
                  have b48504 := hb (x 2 3)
                  have b48505 := hb (x 2 11)
                  clear * - r48503 b48504 b48505 d48495
                  omega
                have d48506 : (x 5 12).toNat = 0 := by
                  have r48507 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48508 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                  have e48509 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                  have b48510 := hb (x 2 3)
                  have b48511 := hb (x 3 2)
                  have b48512 := hb (x 4 13)
                  have b48513 := hb (x 5 12)
                  clear * - r48507 e48508 e48509 b48510 b48511 b48512 b48513 d48502
                  omega
                have d48514 : (x 4 13).toNat = 0 := by
                  have r48515 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48516 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                  have e48517 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                  have b48518 := hb (x 2 3)
                  have b48519 := hb (x 3 2)
                  have b48520 := hb (x 4 13)
                  have b48521 := hb (x 5 12)
                  clear * - r48515 e48516 e48517 b48518 b48519 b48520 b48521 d48506 d48502
                  omega
                have d48522 : (x 3 2).toNat = 0 := by
                  have r48523 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48524 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
                  have e48525 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
                  have b48526 := hb (x 2 3)
                  have b48527 := hb (x 3 2)
                  have b48528 := hb (x 4 13)
                  have b48529 := hb (x 5 12)
                  clear * - r48523 e48524 e48525 b48526 b48527 b48528 b48529 d48506 d48514 d48502
                  omega
                have d48530 : (x 4 1 && x 4 14).toNat = 1 := by
                  have r48531 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b48532 := hb (x 3 2)
                  have b48533 := hb (x 5 13)
                  have b48534 := hb (x 4 1 && x 4 14)
                  clear * - r48531 b48532 b48533 b48534 d48487 d48522
                  omega
                have d48535 : (x 4 14).toNat = 1 := by
                  have r48536 := hand2 (x 4 1) (x 4 14)
                  have b48537 := hb (x 4 14)
                  have b48538 := hb (x 4 1 && x 4 14)
                  clear * - r48536 b48537 b48538 d48530
                  omega
                have d48539 : (x 3 1).toNat = 0 := by
                  have r48540 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b48541 := hb (x 3 1)
                  have b48542 := hb (x 4 14)
                  clear * - r48540 b48541 b48542 d48535
                  omega
                have d48543 : (x 3 1 && x 3 14).toNat = 0 := by
                  have r48544 := hand1 (x 3 1) (x 3 14)
                  have b48545 := hb (x 3 1)
                  have b48546 := hb (x 3 1 && x 3 14)
                  clear * - r48544 b48545 b48546 d48539
                  omega
                have d48547 : (x 2 2).toNat = 1 := by
                  have r48548 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b48549 := hb (x 2 2)
                  have b48550 := hb (x 4 13)
                  have b48551 := hb (x 3 1 && x 3 14)
                  clear * - r48548 b48549 b48550 b48551 d48514 d48543
                  omega
                have d48552 : (x 4 12).toNat = 0 := by
                  have r48553 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48554 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e48555 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b48556 := hb (x 1 3)
                  have b48557 := hb (x 2 2)
                  have b48558 := hb (x 3 13)
                  have b48559 := hb (x 4 12)
                  clear * - r48553 e48554 e48555 b48556 b48557 b48558 b48559 d48547
                  omega
                have d48560 : (x 3 13).toNat = 0 := by
                  have r48561 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48562 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e48563 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b48564 := hb (x 1 3)
                  have b48565 := hb (x 2 2)
                  have b48566 := hb (x 3 13)
                  have b48567 := hb (x 4 12)
                  clear * - r48561 e48562 e48563 b48564 b48565 b48566 b48567 d48552 d48547
                  omega
                have d48568 : (x 1 3).toNat = 0 := by
                  have r48569 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e48570 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                  have e48571 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                  have b48572 := hb (x 1 3)
                  have b48573 := hb (x 2 2)
                  have b48574 := hb (x 3 13)
                  have b48575 := hb (x 4 12)
                  clear * - r48569 e48570 e48571 b48572 b48573 b48574 b48575 d48552 d48560 d48547
                  omega
                have d48576 : (x 1 11).toNat = 0 := by
                  have r48577 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
                  have b48578 := hb (x 1 3)
                  have b48579 := hb (x 1 11)
                  clear * - r48577 b48578 b48579 d48568
                  omega
                have r48580 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b48581 := hb (x (-3) 4)
                have b48582 := hb (x 1 11)
                have b48583 := hb (x 0 1 && x 0 12)
                have b48584 := hb (x (-1) 2 && x (-1) 13)
                have b48585 := hb (x (-2) 3 && x (-2) 14)
                linarith only [r48580, b48581, b48582, b48583, b48584, b48585, d48576, d47651, g32, d48428, d48464]
            · have f48586 : (x 1 1).toNat = 1 := by rw [h47659]; rfl
              have d48587 : (x 2 14).toNat = 0 := by
                have r48588 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b48589 := hb (x 1 1)
                have b48590 := hb (x 2 14)
                clear * - r48588 b48589 b48590 f48586
                omega
              have d48591 : (x 2 1 && x 2 14).toNat = 0 := by
                have r48592 := hand2 (x 2 1) (x 2 14)
                have b48593 := hb (x 2 14)
                have b48594 := hb (x 2 1 && x 2 14)
                clear * - r48592 b48593 b48594 d48587
                omega
              have d48595 : (x 2 2).toNat = 0 := by
                have r48596 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
                have b48597 := hb (x 2 2)
                have b48598 := hb (x 2 14)
                clear * - r48596 b48597 b48598 d48587
                omega
              have d48599 : (x 2 10).toNat = 0 := by
                have r48600 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
                have b48601 := hb (x 2 2)
                have b48602 := hb (x 2 10)
                clear * - r48600 b48601 b48602 d48595
                omega
              have d48603 : (x 3 13).toNat = 1 := by
                have r48604 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b48605 := hb (x 1 2)
                have b48606 := hb (x 3 13)
                have b48607 := hb (x 2 1 && x 2 14)
                clear * - r48604 b48605 b48606 b48607 d48591 g12
                omega
              have d48608 : (x 4 12).toNat = 0 := by
                have r48609 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e48610 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e48611 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b48612 := hb (x 1 3)
                have b48613 := hb (x 2 2)
                have b48614 := hb (x 3 13)
                have b48615 := hb (x 4 12)
                clear * - r48609 e48610 e48611 b48612 b48613 b48614 b48615 d48603 d48595
                omega
              have d48616 : (x 1 3).toNat = 0 := by
                have r48617 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e48618 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
                have e48619 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
                have b48620 := hb (x 1 3)
                have b48621 := hb (x 2 2)
                have b48622 := hb (x 3 13)
                have b48623 := hb (x 4 12)
                clear * - r48617 e48618 e48619 b48620 b48621 b48622 b48623 d48608 d48603 d48595
                omega
              have d48624 : (x 1 11).toNat = 0 := by
                have r48625 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
                have b48626 := hb (x 1 3)
                have b48627 := hb (x 1 11)
                clear * - r48625 b48626 b48627 d48616
                omega
              have d48628 : (x 1 1 && x 1 11).toNat = 0 := by
                have r48629 := hand2 (x 1 1) (x 1 11)
                have b48630 := hb (x 1 11)
                have b48631 := hb (x 1 1 && x 1 11)
                clear * - r48629 b48630 b48631 d48624
                omega
              have r48632 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r48633 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e48634 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e48635 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e48636 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e48637 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e48638 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e48639 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have r48640 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e48641 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
              have e48642 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
              have r48643 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e48644 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
              have e48645 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
              have r48646 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r48647 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r48648 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r48649 := hand2 (x (-2) 4) (x (-2) 8)
              have r48650 := hand2 (x (-3) 5) (x (-3) 9)
              have r48651 := hand2 (x (-4) 6) (x (-4) 10)
              have r48652 := hand2 (x (-5) 7) (x (-5) 11)
              have r48653 := hand1 (x (-6) 8) (x (-6) 12)
              have r48654 := hand1 (x (-7) 9) (x (-7) 13)
              have r48655 := hand1 (x (-4) 2) (x (-4) 12)
              have r48656 := hand1 (x (-5) 3) (x (-5) 13)
              have r48657 := hand1 (x (-6) 4) (x (-6) 14)
              have r48658 := hand2 (x (-2) 2) (x (-2) 12)
              have r48659 := hand2 (x (-3) 3) (x (-3) 13)
              have r48660 := hand1 (x (-2) 4) (x (-2) 14)
              linarith only [r48632, r48633, e48634, e48635, e48636, e48637, e48638, e48639, r48640, e48641, e48642, r48643, e48644, e48645, r48646, r48647, r48648, r48649, r48650, r48651, r48652, r48653, r48654, r48655, r48656, r48657, r48658, r48659, r48660, g1, g3, g4, g9, f47648, f48586, g13, g15, d48599, d47643, g16, g22, g23, g24, d48628, d47655, g25]
          · have f48713 : (x 0 12).toNat = 1 := by rw [h47649]; rfl
            have d48714 : (x (-2) 2).toNat = 0 := by
              have r48715 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e48716 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
              have e48717 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
              have b48718 := hb (x (-3) 3)
              have b48719 := hb (x (-2) 2)
              have b48720 := hb (x (-1) 13)
              have b48721 := hb (x 0 12)
              clear * - r48715 e48716 e48717 b48718 b48719 b48720 b48721 f48713 g7
              omega
            have d48722 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
              have r48723 := hand1 (x (-2) 2) (x (-2) 13)
              have b48724 := hb (x (-2) 2)
              have b48725 := hb (x (-2) 2 && x (-2) 13)
              clear * - r48723 b48724 b48725 d48714
              omega
            have d48726 : (x (-3) 3).toNat = 0 := by
              have r48727 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e48728 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
              have e48729 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
              have b48730 := hb (x (-3) 3)
              have b48731 := hb (x (-2) 2)
              have b48732 := hb (x (-1) 13)
              have b48733 := hb (x 0 12)
              clear * - r48727 e48728 e48729 b48730 b48731 b48732 b48733 f48713 g7 d48714
              omega
            have d48734 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
              have r48735 := hand1 (x (-3) 3) (x (-3) 14)
              have b48736 := hb (x (-3) 3)
              have b48737 := hb (x (-3) 3 && x (-3) 14)
              clear * - r48735 b48736 b48737 d48726
              omega
            have r48738 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48739 := hb (x (-4) 4)
            have b48740 := hb (x 0 11)
            have b48741 := hb (x (-1) 1 && x (-1) 12)
            have b48742 := hb (x (-2) 2 && x (-2) 13)
            have b48743 := hb (x (-3) 3 && x (-3) 14)
            linarith only [r48738, b48739, b48740, b48741, b48742, b48743, d47617, g31, d48722, d48734, g2]
        · have f48744 : (x 0 10).toNat = 1 := by rw [h47647]; rfl
          have d48745 : (x 2 8).toNat = 0 := by
            have r48746 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48747 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e48748 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e48749 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e48750 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e48751 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e48752 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b48753 := hb (x (-5) 7)
            have b48754 := hb (x (-4) 6)
            have b48755 := hb (x (-3) 5)
            have b48756 := hb (x (-2) 4)
            have b48757 := hb (x (-1) 11)
            have b48758 := hb (x 0 10)
            have b48759 := hb (x 1 9)
            have b48760 := hb (x 2 8)
            clear * - r48746 e48747 e48748 e48749 e48750 e48751 e48752 b48753 b48754 b48755 b48756 b48757 b48758 b48759 b48760 f48744 g6
            omega
          have d48761 : (x 1 9).toNat = 0 := by
            have r48762 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48763 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e48764 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e48765 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e48766 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e48767 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e48768 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b48769 := hb (x (-5) 7)
            have b48770 := hb (x (-4) 6)
            have b48771 := hb (x (-3) 5)
            have b48772 := hb (x (-2) 4)
            have b48773 := hb (x (-1) 11)
            have b48774 := hb (x 0 10)
            have b48775 := hb (x 1 9)
            have b48776 := hb (x 2 8)
            clear * - r48762 e48763 e48764 e48765 e48766 e48767 e48768 b48769 b48770 b48771 b48772 b48773 b48774 b48775 b48776 d48745 f48744 g6
            omega
          have d48777 : (x (-2) 4).toNat = 0 := by
            have r48778 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48779 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e48780 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e48781 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e48782 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e48783 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e48784 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b48785 := hb (x (-5) 7)
            have b48786 := hb (x (-4) 6)
            have b48787 := hb (x (-3) 5)
            have b48788 := hb (x (-2) 4)
            have b48789 := hb (x (-1) 11)
            have b48790 := hb (x 0 10)
            have b48791 := hb (x 1 9)
            have b48792 := hb (x 2 8)
            clear * - r48778 e48779 e48780 e48781 e48782 e48783 e48784 b48785 b48786 b48787 b48788 b48789 b48790 b48791 b48792 d48745 d48761 f48744 g6
            omega
          have d48793 : (x (-2) 4 && x (-2) 13).toNat = 0 := by
            have r48794 := hand1 (x (-2) 4) (x (-2) 13)
            have b48795 := hb (x (-2) 4)
            have b48796 := hb (x (-2) 4 && x (-2) 13)
            clear * - r48794 b48795 b48796 d48777
            omega
          have d48797 : (x (-3) 5).toNat = 0 := by
            have r48798 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48799 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e48800 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e48801 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e48802 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e48803 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e48804 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b48805 := hb (x (-5) 7)
            have b48806 := hb (x (-4) 6)
            have b48807 := hb (x (-3) 5)
            have b48808 := hb (x (-2) 4)
            have b48809 := hb (x (-1) 11)
            have b48810 := hb (x 0 10)
            have b48811 := hb (x 1 9)
            have b48812 := hb (x 2 8)
            clear * - r48798 e48799 e48800 e48801 e48802 e48803 e48804 b48805 b48806 b48807 b48808 b48809 b48810 b48811 b48812 d48745 d48761 f48744 g6 d48777
            omega
          have d48813 : (x (-3) 5 && x (-3) 14).toNat = 0 := by
            have r48814 := hand1 (x (-3) 5) (x (-3) 14)
            have b48815 := hb (x (-3) 5)
            have b48816 := hb (x (-3) 5 && x (-3) 14)
            clear * - r48814 b48815 b48816 d48797
            omega
          have d48817 : (x (-4) 6).toNat = 0 := by
            have r48818 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48819 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
            have e48820 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
            have e48821 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
            have e48822 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
            have e48823 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
            have e48824 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
            have b48825 := hb (x (-5) 7)
            have b48826 := hb (x (-4) 6)
            have b48827 := hb (x (-3) 5)
            have b48828 := hb (x (-2) 4)
            have b48829 := hb (x (-1) 11)
            have b48830 := hb (x 0 10)
            have b48831 := hb (x 1 9)
            have b48832 := hb (x 2 8)
            clear * - r48818 e48819 e48820 e48821 e48822 e48823 e48824 b48825 b48826 b48827 b48828 b48829 b48830 b48831 b48832 d48745 d48761 f48744 g6 d48777 d48797
            omega
          have d48833 : (x 2 9).toNat = 1 := by
            have r48834 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48835 := hb (x (-4) 6)
            have b48836 := hb (x 2 9)
            have b48837 := hb (x 1 1 && x 1 10)
            have b48838 := hb (x 0 2 && x 0 11)
            have b48839 := hb (x (-1) 3 && x (-1) 12)
            have b48840 := hb (x (-2) 4 && x (-2) 13)
            have b48841 := hb (x (-3) 5 && x (-3) 14)
            clear * - r48834 b48835 b48836 b48837 b48838 b48839 b48840 b48841 g20 d47625 g21 d48793 d48813 d48817
            omega
          have d48842 : (x 2 1).toNat = 1 := by
            have r48843 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
            have b48844 := hb (x 2 1)
            have b48845 := hb (x 2 9)
            clear * - r48843 b48844 b48845 d48833
            omega
          have d48846 : (x 3 14).toNat = 0 := by
            have r48847 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48848 := hb (x 2 1)
            have b48849 := hb (x 3 14)
            clear * - r48847 b48848 b48849 d48842
            omega
          have d48850 : (x 3 2).toNat = 0 := by
            have r48851 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
            have b48852 := hb (x 3 2)
            have b48853 := hb (x 3 14)
            clear * - r48851 b48852 b48853 d48846
            omega
          have d48854 : (x 3 8).toNat = 0 := by
            have r48855 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48856 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
            have e48857 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
            have e48858 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
            have e48859 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
            have e48860 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
            have e48861 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
            have b48862 := hb (x (-4) 7)
            have b48863 := hb (x (-3) 6)
            have b48864 := hb (x (-2) 5)
            have b48865 := hb (x (-1) 4)
            have b48866 := hb (x 0 11)
            have b48867 := hb (x 1 10)
            have b48868 := hb (x 2 9)
            have b48869 := hb (x 3 8)
            clear * - r48855 e48856 e48857 e48858 e48859 e48860 e48861 b48862 b48863 b48864 b48865 b48866 b48867 b48868 b48869 d48833 g14 d47617
            omega
          have d48870 : (x (-1) 4).toNat = 0 := by
            have r48871 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48872 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
            have e48873 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
            have e48874 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
            have e48875 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
            have e48876 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
            have e48877 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
            have b48878 := hb (x (-4) 7)
            have b48879 := hb (x (-3) 6)
            have b48880 := hb (x (-2) 5)
            have b48881 := hb (x (-1) 4)
            have b48882 := hb (x 0 11)
            have b48883 := hb (x 1 10)
            have b48884 := hb (x 2 9)
            have b48885 := hb (x 3 8)
            clear * - r48871 e48872 e48873 e48874 e48875 e48876 e48877 b48878 b48879 b48880 b48881 b48882 b48883 b48884 b48885 d48854 d48833 g14 d47617
            omega
          have d48886 : (x 3 11).toNat = 1 := by
            have r48887 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48888 := hb (x (-1) 4)
            have b48889 := hb (x 3 11)
            have b48890 := hb (x 2 1 && x 2 12)
            have b48891 := hb (x 1 2 && x 1 13)
            have b48892 := hb (x 0 3 && x 0 14)
            clear * - r48887 b48888 b48889 b48890 b48891 b48892 g34 g35 d47609 d48870
            omega
          have d48893 : (x 3 3).toNat = 1 := by
            have r48894 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
            have b48895 := hb (x 3 3)
            have b48896 := hb (x 3 11)
            clear * - r48894 b48895 b48896 d48886
            omega
          have d48897 : (x 6 12).toNat = 0 := by
            have r48898 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48899 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e48900 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b48901 := hb (x 3 3)
            have b48902 := hb (x 4 2)
            have b48903 := hb (x 5 13)
            have b48904 := hb (x 6 12)
            clear * - r48898 e48899 e48900 b48901 b48902 b48903 b48904 d48893
            omega
          have d48905 : (x 5 13).toNat = 0 := by
            have r48906 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e48907 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e48908 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b48909 := hb (x 3 3)
            have b48910 := hb (x 4 2)
            have b48911 := hb (x 5 13)
            have b48912 := hb (x 6 12)
            clear * - r48906 e48907 e48908 b48909 b48910 b48911 b48912 d48897 d48893
            omega
          have d48913 : (x 4 1 && x 4 14).toNat = 1 := by
            have r48914 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48915 := hb (x 3 2)
            have b48916 := hb (x 5 13)
            have b48917 := hb (x 4 1 && x 4 14)
            clear * - r48914 b48915 b48916 b48917 d48905 d48850
            omega
          have d48918 : (x 4 14).toNat = 1 := by
            have r48919 := hand2 (x 4 1) (x 4 14)
            have b48920 := hb (x 4 14)
            have b48921 := hb (x 4 1 && x 4 14)
            clear * - r48919 b48920 b48921 d48913
            omega
          have d48922 : (x 3 1).toNat = 0 := by
            have r48923 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48924 := hb (x 3 1)
            have b48925 := hb (x 4 14)
            clear * - r48923 b48924 b48925 d48918
            omega
          have d48926 : (x 3 1 && x 3 11).toNat = 0 := by
            have r48927 := hand1 (x 3 1) (x 3 11)
            have b48928 := hb (x 3 1)
            have b48929 := hb (x 3 1 && x 3 11)
            clear * - r48927 b48928 b48929 d48922
            omega
          have d48930 : (x 4 10).toNat = 1 := by
            have r48931 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b48932 := hb (x (-1) 5)
            have b48933 := hb (x 4 10)
            have b48934 := hb (x 3 1 && x 3 11)
            have b48935 := hb (x 2 2 && x 2 12)
            have b48936 := hb (x 1 3 && x 1 13)
            have b48937 := hb (x 0 4 && x 0 14)
            clear * - r48931 b48932 b48933 b48934 b48935 b48936 b48937 d48926 g27 g28 d47631 g5
            omega
          have d48938 : (x 4 2).toNat = 1 := by
            have r48939 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
            have b48940 := hb (x 4 2)
            have b48941 := hb (x 4 10)
            clear * - r48939 b48940 b48941 d48930
            omega
          have r48942 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48943 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e48944 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b48945 := hb (x 3 3)
          have b48946 := hb (x 4 2)
          have b48947 := hb (x 5 13)
          have b48948 := hb (x 6 12)
          linarith only [r48942, e48943, e48944, b48945, b48946, b48947, b48948, d48897, d48905, d48938, d48893]
      · have f48949 : (x 0 6).toNat = 1 := by rw [h47637]; rfl
        have d48950 : (x 6 8).toNat = 0 := by
          have r48951 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48952 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e48953 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e48954 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e48955 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e48956 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e48957 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b48958 := hb (x (-1) 7)
          have b48959 := hb (x 0 6)
          have b48960 := hb (x 1 5)
          have b48961 := hb (x 2 4)
          have b48962 := hb (x 3 11)
          have b48963 := hb (x 4 10)
          have b48964 := hb (x 5 9)
          have b48965 := hb (x 6 8)
          clear * - r48951 e48952 e48953 e48954 e48955 e48956 e48957 b48958 b48959 b48960 b48961 b48962 b48963 b48964 b48965 g15 g13 f48949
          omega
        have d48966 : (x 5 9).toNat = 0 := by
          have r48967 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48968 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e48969 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e48970 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e48971 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e48972 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e48973 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b48974 := hb (x (-1) 7)
          have b48975 := hb (x 0 6)
          have b48976 := hb (x 1 5)
          have b48977 := hb (x 2 4)
          have b48978 := hb (x 3 11)
          have b48979 := hb (x 4 10)
          have b48980 := hb (x 5 9)
          have b48981 := hb (x 6 8)
          clear * - r48967 e48968 e48969 e48970 e48971 e48972 e48973 b48974 b48975 b48976 b48977 b48978 b48979 b48980 b48981 d48950 g15 g13 f48949
          omega
        have d48982 : (x 4 10).toNat = 0 := by
          have r48983 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e48984 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e48985 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e48986 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e48987 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e48988 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e48989 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b48990 := hb (x (-1) 7)
          have b48991 := hb (x 0 6)
          have b48992 := hb (x 1 5)
          have b48993 := hb (x 2 4)
          have b48994 := hb (x 3 11)
          have b48995 := hb (x 4 10)
          have b48996 := hb (x 5 9)
          have b48997 := hb (x 6 8)
          clear * - r48983 e48984 e48985 e48986 e48987 e48988 e48989 b48990 b48991 b48992 b48993 b48994 b48995 b48996 b48997 d48950 d48966 g15 g13 f48949
          omega
        have d48998 : (x 3 1 && x 3 11).toNat = 1 := by
          have r48999 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b49000 := hb (x (-1) 5)
          have b49001 := hb (x 4 10)
          have b49002 := hb (x 3 1 && x 3 11)
          have b49003 := hb (x 2 2 && x 2 12)
          have b49004 := hb (x 1 3 && x 1 13)
          have b49005 := hb (x 0 4 && x 0 14)
          clear * - r48999 b49000 b49001 b49002 b49003 b49004 b49005 d48982 g27 g28 d47631 g5
          omega
        have d49006 : (x 3 11).toNat = 1 := by
          have r49007 := hand2 (x 3 1) (x 3 11)
          have b49008 := hb (x 3 11)
          have b49009 := hb (x 3 1 && x 3 11)
          clear * - r49007 b49008 b49009 d48998
          omega
        have r49010 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49011 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e49012 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e49013 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e49014 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e49015 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e49016 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b49017 := hb (x (-1) 7)
        have b49018 := hb (x 0 6)
        have b49019 := hb (x 1 5)
        have b49020 := hb (x 2 4)
        have b49021 := hb (x 3 11)
        have b49022 := hb (x 4 10)
        have b49023 := hb (x 5 9)
        have b49024 := hb (x 6 8)
        linarith only [r49010, e49011, e49012, e49013, e49014, e49015, e49016, b49017, b49018, b49019, b49020, b49021, b49022, b49023, b49024, d48950, d48966, d48982, d49006, g15, g13, f48949]
    · have f49025 : (x 0 5).toNat = 1 := by rw [h47635]; rfl
      have d49026 : (x 0 13).toNat = 1 := by
        have r49027 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
        have b49028 := hb (x 0 5)
        have b49029 := hb (x 0 13)
        clear * - r49027 b49028 b49029 f49025
        omega
      have d49030 : (x 1 12).toNat = 0 := by
        have r49031 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49032 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e49033 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b49034 := hb (x (-2) 3)
        have b49035 := hb (x (-1) 2)
        have b49036 := hb (x 0 13)
        have b49037 := hb (x 1 12)
        clear * - r49031 e49032 e49033 b49034 b49035 b49036 b49037 d49026
        omega
      have d49038 : (x 1 4).toNat = 0 := by
        have r49039 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
        have b49040 := hb (x 1 4)
        have b49041 := hb (x 1 12)
        clear * - r49039 b49040 b49041 d49030
        omega
      have d49042 : (x (-1) 2).toNat = 0 := by
        have r49043 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49044 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e49045 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b49046 := hb (x (-2) 3)
        have b49047 := hb (x (-1) 2)
        have b49048 := hb (x 0 13)
        have b49049 := hb (x 1 12)
        clear * - r49043 e49044 e49045 b49046 b49047 b49048 b49049 d49030 d49026
        omega
      have d49050 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
        have r49051 := hand1 (x (-1) 2) (x (-1) 12)
        have b49052 := hb (x (-1) 2)
        have b49053 := hb (x (-1) 2 && x (-1) 12)
        clear * - r49051 b49052 b49053 d49042
        omega
      have d49054 : (x (-2) 3).toNat = 0 := by
        have r49055 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49056 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
        have e49057 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
        have b49058 := hb (x (-2) 3)
        have b49059 := hb (x (-1) 2)
        have b49060 := hb (x 0 13)
        have b49061 := hb (x 1 12)
        clear * - r49055 e49056 e49057 b49058 b49059 b49060 b49061 d49030 d49026 d49042
        omega
      have d49062 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
        have r49063 := hand1 (x (-2) 3) (x (-2) 13)
        have b49064 := hb (x (-2) 3)
        have b49065 := hb (x (-2) 3 && x (-2) 13)
        clear * - r49063 b49064 b49065 d49054
        omega
      have d49066 : (x (-2) 11).toNat = 0 := by
        have r49067 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
        have b49068 := hb (x (-2) 3)
        have b49069 := hb (x (-2) 11)
        clear * - r49067 b49068 b49069 d49054
        omega
      have d49070 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
        have r49071 := hand2 (x (-2) 2) (x (-2) 11)
        have b49072 := hb (x (-2) 11)
        have b49073 := hb (x (-2) 2 && x (-2) 11)
        clear * - r49071 b49072 b49073 d49066
        omega
      have d49074 : (x (-3) 3 && x (-3) 12).toNat = 1 := by
        have r49075 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49076 := hb (x (-6) 6)
        have b49077 := hb (x 0 9)
        have b49078 := hb (x (-1) 1 && x (-1) 10)
        have b49079 := hb (x (-2) 2 && x (-2) 11)
        have b49080 := hb (x (-3) 3 && x (-3) 12)
        have b49081 := hb (x (-4) 4 && x (-4) 13)
        have b49082 := hb (x (-5) 5 && x (-5) 14)
        clear * - r49075 b49076 b49077 b49078 b49079 b49080 b49081 b49082 g11 g17 d49070 g18 g19 g0
        omega
      have d49083 : (x (-3) 12).toNat = 1 := by
        have r49084 := hand2 (x (-3) 3) (x (-3) 12)
        have b49085 := hb (x (-3) 12)
        have b49086 := hb (x (-3) 3 && x (-3) 12)
        clear * - r49084 b49085 b49086 d49074
        omega
      have d49087 : (x (-4) 13).toNat = 0 := by
        have r49088 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49089 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e49090 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b49091 := hb (x (-6) 3)
        have b49092 := hb (x (-5) 2)
        have b49093 := hb (x (-4) 13)
        have b49094 := hb (x (-3) 12)
        clear * - r49088 e49089 e49090 b49091 b49092 b49093 b49094 d49083
        omega
      have d49095 : (x (-4) 5).toNat = 0 := by
        have r49096 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
        have b49097 := hb (x (-4) 5)
        have b49098 := hb (x (-4) 13)
        clear * - r49096 b49097 b49098 d49087
        omega
      have d49099 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
        have r49100 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49101 := hb (x (-4) 5)
        have b49102 := hb (x 1 10)
        have b49103 := hb (x 0 1 && x 0 11)
        have b49104 := hb (x (-1) 2 && x (-1) 12)
        have b49105 := hb (x (-2) 3 && x (-2) 13)
        have b49106 := hb (x (-3) 4 && x (-3) 14)
        clear * - r49100 b49101 b49102 b49103 b49104 b49105 b49106 g14 d47621 d49050 d49062 d49095
        omega
      have d49107 : (x (-3) 14).toNat = 1 := by
        have r49108 := hand2 (x (-3) 4) (x (-3) 14)
        have b49109 := hb (x (-3) 14)
        have b49110 := hb (x (-3) 4 && x (-3) 14)
        clear * - r49108 b49109 b49110 d49099
        omega
      have d49111 : (x (-4) 1).toNat = 0 := by
        have r49112 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49113 := hb (x (-4) 1)
        have b49114 := hb (x (-3) 14)
        clear * - r49112 b49113 b49114 d49107
        omega
      have d49115 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
        have r49116 := hand1 (x (-4) 1) (x (-4) 14)
        have b49117 := hb (x (-4) 1)
        have b49118 := hb (x (-4) 1 && x (-4) 14)
        clear * - r49116 b49117 b49118 d49111
        omega
      have d49119 : (x (-5) 2).toNat = 0 := by
        have r49120 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49121 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e49122 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b49123 := hb (x (-6) 3)
        have b49124 := hb (x (-5) 2)
        have b49125 := hb (x (-4) 13)
        have b49126 := hb (x (-3) 12)
        clear * - r49120 e49121 e49122 b49123 b49124 b49125 b49126 d49083 d49087
        omega
      have d49127 : (x (-3) 13).toNat = 1 := by
        have r49128 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49129 := hb (x (-5) 2)
        have b49130 := hb (x (-3) 13)
        have b49131 := hb (x (-4) 1 && x (-4) 14)
        clear * - r49128 b49129 b49130 b49131 d49115 d49119
        omega
      have d49132 : (x (-3) 1).toNat = 1 := by
        have r49133 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
        have b49134 := hb (x (-3) 1)
        have b49135 := hb (x (-3) 13)
        clear * - r49133 b49134 b49135 d49127
        omega
      have d49136 : (x (-2) 14).toNat = 0 := by
        have r49137 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49138 := hb (x (-3) 1)
        have b49139 := hb (x (-2) 14)
        clear * - r49137 b49138 b49139 d49132
        omega
      have d49140 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
        have r49141 := hand2 (x (-2) 1) (x (-2) 14)
        have b49142 := hb (x (-2) 14)
        have b49143 := hb (x (-2) 1 && x (-2) 14)
        clear * - r49141 b49142 b49143 d49136
        omega
      have d49144 : (x (-3) 2).toNat = 1 := by
        have r49145 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49146 := hb (x (-3) 2)
        have b49147 := hb (x (-1) 13)
        have b49148 := hb (x (-2) 1 && x (-2) 14)
        clear * - r49145 b49146 b49147 b49148 g7 d49140
        omega
      have d49149 : (x (-1) 12).toNat = 0 := by
        have r49150 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49151 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e49152 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b49153 := hb (x (-4) 3)
        have b49154 := hb (x (-3) 2)
        have b49155 := hb (x (-2) 13)
        have b49156 := hb (x (-1) 12)
        clear * - r49150 e49151 e49152 b49153 b49154 b49155 b49156 d49144
        omega
      have d49157 : (x (-1) 4).toNat = 0 := by
        have r49158 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
        have b49159 := hb (x (-1) 4)
        have b49160 := hb (x (-1) 12)
        clear * - r49158 b49159 b49160 d49149
        omega
      have d49161 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
        have r49162 := hand1 (x (-1) 4) (x (-1) 14)
        have b49163 := hb (x (-1) 4)
        have b49164 := hb (x (-1) 4 && x (-1) 14)
        clear * - r49162 b49163 b49164 d49157
        omega
      have d49165 : (x 3 11).toNat = 1 := by
        have r49166 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49167 := hb (x (-1) 4)
        have b49168 := hb (x 3 11)
        have b49169 := hb (x 2 1 && x 2 12)
        have b49170 := hb (x 1 2 && x 1 13)
        have b49171 := hb (x 0 3 && x 0 14)
        clear * - r49166 b49167 b49168 b49169 b49170 b49171 g34 g35 d47609 d49157
        omega
      have d49172 : (x 3 3).toNat = 1 := by
        have r49173 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
        have b49174 := hb (x 3 3)
        have b49175 := hb (x 3 11)
        clear * - r49173 b49174 b49175 d49165
        omega
      have d49176 : (x 6 12).toNat = 0 := by
        have r49177 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49178 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e49179 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b49180 := hb (x 3 3)
        have b49181 := hb (x 4 2)
        have b49182 := hb (x 5 13)
        have b49183 := hb (x 6 12)
        clear * - r49177 e49178 e49179 b49180 b49181 b49182 b49183 d49172
        omega
      have d49184 : (x 5 13).toNat = 0 := by
        have r49185 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49186 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e49187 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b49188 := hb (x 3 3)
        have b49189 := hb (x 4 2)
        have b49190 := hb (x 5 13)
        have b49191 := hb (x 6 12)
        clear * - r49185 e49186 e49187 b49188 b49189 b49190 b49191 d49176 d49172
        omega
      have d49192 : (x 4 2).toNat = 0 := by
        have r49193 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49194 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e49195 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b49196 := hb (x 3 3)
        have b49197 := hb (x 4 2)
        have b49198 := hb (x 5 13)
        have b49199 := hb (x 6 12)
        clear * - r49193 e49194 e49195 b49196 b49197 b49198 b49199 d49176 d49184 d49172
        omega
      have d49200 : (x 4 10).toNat = 0 := by
        have r49201 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
        have b49202 := hb (x 4 2)
        have b49203 := hb (x 4 10)
        clear * - r49201 b49202 b49203 d49192
        omega
      have d49204 : (x 3 1 && x 3 11).toNat = 1 := by
        have r49205 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49206 := hb (x (-1) 5)
        have b49207 := hb (x 4 10)
        have b49208 := hb (x 3 1 && x 3 11)
        have b49209 := hb (x 2 2 && x 2 12)
        have b49210 := hb (x 1 3 && x 1 13)
        have b49211 := hb (x 0 4 && x 0 14)
        clear * - r49205 b49206 b49207 b49208 b49209 b49210 b49211 d49200 g27 g28 d47631 g5
        omega
      have d49212 : (x 3 1).toNat = 1 := by
        have r49213 := hand1 (x 3 1) (x 3 11)
        have b49214 := hb (x 3 1)
        have b49215 := hb (x 3 1 && x 3 11)
        clear * - r49213 b49214 b49215 d49204
        omega
      have d49216 : (x 4 14).toNat = 0 := by
        have r49217 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49218 := hb (x 3 1)
        have b49219 := hb (x 4 14)
        clear * - r49217 b49218 b49219 d49212
        omega
      have d49220 : (x 4 1 && x 4 14).toNat = 0 := by
        have r49221 := hand2 (x 4 1) (x 4 14)
        have b49222 := hb (x 4 14)
        have b49223 := hb (x 4 1 && x 4 14)
        clear * - r49221 b49222 b49223 d49216
        omega
      have d49224 : (x 3 2).toNat = 1 := by
        have r49225 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49226 := hb (x 3 2)
        have b49227 := hb (x 5 13)
        have b49228 := hb (x 4 1 && x 4 14)
        clear * - r49225 b49226 b49227 b49228 d49184 d49220
        omega
      have d49229 : (x 3 14).toNat = 1 := by
        have r49230 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
        have b49231 := hb (x 3 2)
        have b49232 := hb (x 3 14)
        clear * - r49230 b49231 b49232 d49224
        omega
      have d49233 : (x 2 1).toNat = 0 := by
        have r49234 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49235 := hb (x 2 1)
        have b49236 := hb (x 3 14)
        clear * - r49234 b49235 b49236 d49229
        omega
      have d49237 : (x 2 1 && x 2 11).toNat = 0 := by
        have r49238 := hand1 (x 2 1) (x 2 11)
        have b49239 := hb (x 2 1)
        have b49240 := hb (x 2 1 && x 2 11)
        clear * - r49238 b49239 b49240 d49233
        omega
      have d49241 : (x 5 12).toNat = 0 := by
        have r49242 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49243 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e49244 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b49245 := hb (x 2 3)
        have b49246 := hb (x 3 2)
        have b49247 := hb (x 4 13)
        have b49248 := hb (x 5 12)
        clear * - r49242 e49243 e49244 b49245 b49246 b49247 b49248 d49224
        omega
      have d49249 : (x 4 13).toNat = 0 := by
        have r49250 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49251 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e49252 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b49253 := hb (x 2 3)
        have b49254 := hb (x 3 2)
        have b49255 := hb (x 4 13)
        have b49256 := hb (x 5 12)
        clear * - r49250 e49251 e49252 b49253 b49254 b49255 b49256 d49241 d49224
        omega
      have d49257 : (x 2 3).toNat = 0 := by
        have r49258 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49259 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e49260 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b49261 := hb (x 2 3)
        have b49262 := hb (x 3 2)
        have b49263 := hb (x 4 13)
        have b49264 := hb (x 5 12)
        clear * - r49258 e49259 e49260 b49261 b49262 b49263 b49264 d49241 d49249 d49224
        omega
      have d49265 : (x 2 11).toNat = 0 := by
        have r49266 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
        have b49267 := hb (x 2 3)
        have b49268 := hb (x 2 11)
        clear * - r49266 b49267 b49268 d49257
        omega
      have d49269 : (x (-2) 13).toNat = 0 := by
        have r49270 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e49271 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e49272 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b49273 := hb (x (-4) 3)
        have b49274 := hb (x (-3) 2)
        have b49275 := hb (x (-2) 13)
        have b49276 := hb (x (-1) 12)
        clear * - r49270 e49271 e49272 b49273 b49274 b49275 b49276 d49149 d49144
        omega
      have d49277 : (x (-2) 5).toNat = 0 := by
        have r49278 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
        have b49279 := hb (x (-2) 5)
        have b49280 := hb (x (-2) 13)
        clear * - r49278 b49279 b49280 d49269
        omega
      have d49281 : (x 3 10).toNat = 1 := by
        have r49282 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b49283 := hb (x (-2) 5)
        have b49284 := hb (x 3 10)
        have b49285 := hb (x 2 1 && x 2 11)
        have b49286 := hb (x 1 2 && x 1 12)
        have b49287 := hb (x 0 3 && x 0 13)
        have b49288 := hb (x (-1) 4 && x (-1) 14)
        clear * - r49282 b49283 b49284 b49285 b49286 b49287 b49288 d49237 g26 d47613 d49161 d49277
        omega
      have r49289 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49290 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
      have e49291 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
      have e49292 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
      have e49293 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
      have e49294 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
      have e49295 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
      have b49296 := hb (x (-2) 7)
      have b49297 := hb (x (-1) 6)
      have b49298 := hb (x 0 5)
      have b49299 := hb (x 1 4)
      have b49300 := hb (x 2 11)
      have b49301 := hb (x 3 10)
      have b49302 := hb (x 4 9)
      have b49303 := hb (x 5 8)
      linarith only [r49289, e49290, e49291, e49292, e49293, e49294, e49295, b49296, b49297, b49298, b49299, b49300, b49301, b49302, b49303, d49281, d49265, d49038, f49025]
  · have f49304 : (x 0 4).toNat = 1 := by rw [h47629]; rfl
    have d49305 : (x 0 12).toNat = 1 := by
      have r49306 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
      have b49307 := hb (x 0 4)
      have b49308 := hb (x 0 12)
      clear * - r49306 b49307 b49308 f49304
      omega
    have d49309 : (x (-2) 2).toNat = 0 := by
      have r49310 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49311 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e49312 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b49313 := hb (x (-3) 3)
      have b49314 := hb (x (-2) 2)
      have b49315 := hb (x (-1) 13)
      have b49316 := hb (x 0 12)
      clear * - r49310 e49311 e49312 b49313 b49314 b49315 b49316 d49305 g7
      omega
    have d49317 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
      have r49318 := hand1 (x (-2) 2) (x (-2) 13)
      have b49319 := hb (x (-2) 2)
      have b49320 := hb (x (-2) 2 && x (-2) 13)
      clear * - r49318 b49319 b49320 d49309
      omega
    have d49321 : (x (-3) 3).toNat = 0 := by
      have r49322 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e49323 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e49324 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b49325 := hb (x (-3) 3)
      have b49326 := hb (x (-2) 2)
      have b49327 := hb (x (-1) 13)
      have b49328 := hb (x 0 12)
      clear * - r49322 e49323 e49324 b49325 b49326 b49327 b49328 d49305 g7 d49309
      omega
    have d49329 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
      have r49330 := hand1 (x (-3) 3) (x (-3) 14)
      have b49331 := hb (x (-3) 3)
      have b49332 := hb (x (-3) 3 && x (-3) 14)
      clear * - r49330 b49331 b49332 d49321
      omega
    have r49333 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b49334 := hb (x (-4) 4)
    have b49335 := hb (x 0 11)
    have b49336 := hb (x (-1) 1 && x (-1) 12)
    have b49337 := hb (x (-2) 2 && x (-2) 13)
    have b49338 := hb (x (-3) 3 && x (-3) 14)
    linarith only [r49333, b49334, b49335, b49336, b49337, b49338, d47617, g31, d49317, d49329, g2]

theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a01110 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-5) 5).toNat = 0)
    (g2 : (x (-4) 4).toNat = 0)
    (g3 : (x (-2) 10).toNat = 0)
    (g4 : (x (-1) 3).toNat = 0)
    (g5 : (x (-1) 5).toNat = 0)
    (g6 : (x (-1) 11).toNat = 0)
    (g7 : (x (-1) 13).toNat = 0)
    (g8 : (x 0 1).toNat = 1)
    (g9 : (x 0 2).toNat = 1)
    (g10 : (x 0 3).toNat = 0)
    (g11 : (x 0 9).toNat = 0)
    (g12 : (x 1 2).toNat = 0)
    (g13 : (x 1 5).toNat = 0)
    (g14 : (x 1 10).toNat = 0)
    (g15 : (x 2 4).toNat = 0)
    (g16 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g17 : (x (-1) 1 && x (-1) 10).toNat = 0)
    (g18 : (x (-4) 4 && x (-4) 13).toNat = 0)
    (g19 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g20 : (x 1 1 && x 1 10).toNat = 0)
    (g21 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g22 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g23 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g24 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g25 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g26 : (x 1 2 && x 1 12).toNat = 0)
    (g27 : (x 2 2 && x 2 12).toNat = 0)
    (g28 : (x 1 3 && x 1 13).toNat = 0)
    (g29 : (x 1 4 && x 1 14).toNat = 0)
    (g30 : (x 2 4 && x 2 14).toNat = 0)
    (g31 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g32 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g33 : (x (-1) 3 && x (-1) 14).toNat = 0)
    (g34 : (x 2 1 && x 2 12).toNat = 0)
    (g35 : (x 1 2 && x 1 13).toNat = 0)
    (g36 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a01110_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36
