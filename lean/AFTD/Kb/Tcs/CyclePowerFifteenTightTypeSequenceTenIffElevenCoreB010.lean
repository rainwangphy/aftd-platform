import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b010

Topic: combinatorics   Node: 037c8aac0a42

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core: under the layer-free tight-cover constraints for k = 15 and 29 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b010_aux (x : ℤ → Fin 16 → Bool)
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
    (g2 : (x (-2) 5).toNat = 0)
    (g3 : (x (-2) 10).toNat = 0)
    (g4 : (x (-1) 5).toNat = 0)
    (g5 : (x (-1) 13).toNat = 0)
    (g6 : (x 0 1).toNat = 0)
    (g7 : (x 0 5).toNat = 0)
    (g8 : (x 1 2).toNat = 0)
    (g9 : (x 1 10).toNat = 0)
    (g10 : (x 2 5).toNat = 0)
    (g11 : (x 2 13).toNat = 0)
    (g12 : (x 3 4).toNat = 0)
    (g13 : (x 4 1 && x 4 8).toNat = 0)
    (g14 : (x 3 2 && x 3 9).toNat = 0)
    (g15 : (x 2 3 && x 2 10).toNat = 0)
    (g16 : (x 1 4 && x 1 11).toNat = 0)
    (g17 : (x 0 5 && x 0 12).toNat = 0)
    (g18 : (x (-1) 6 && x (-1) 13).toNat = 0)
    (g19 : (x 3 4 && x 3 11).toNat = 0)
    (g20 : (x 2 5 && x 2 12).toNat = 0)
    (g21 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g22 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g23 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g24 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g25 : (x 1 2 && x 1 12).toNat = 0)
    (g26 : (x (-1) 4 && x (-1) 14).toNat = 0)
    (g27 : (x 3 2 && x 3 12).toNat = 0)
    (g28 : (x 2 3 && x 2 13).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d11252 : (x 0 1 && x 0 11).toNat = 0 := by
    have r11253 := hand1 (x 0 1) (x 0 11)
    have b11254 := hb (x 0 1)
    have b11255 := hb (x 0 1 && x 0 11)
    clear * - r11253 b11254 b11255 g6
    omega
  have d11256 : (x 0 13).toNat = 0 := by
    have r11257 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
    have b11258 := hb (x 0 1)
    have b11259 := hb (x 0 13)
    clear * - r11257 b11258 b11259 g6
    omega
  have d11260 : (x 0 3 && x 0 13).toNat = 0 := by
    have r11261 := hand2 (x 0 3) (x 0 13)
    have b11262 := hb (x 0 13)
    have b11263 := hb (x 0 3 && x 0 13)
    clear * - r11261 b11262 b11263 d11256
    omega
  have d11264 : (x 0 9).toNat = 0 := by
    have r11265 : (x 0 9).toNat ≤ (x 0 1).toNat := himp _ _ (hp9 0)
    have b11266 := hb (x 0 1)
    have b11267 := hb (x 0 9)
    clear * - r11265 b11266 b11267 g6
    omega
  have d11268 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
    have r11269 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11270 := hb (x (-2) 2)
    have b11271 := hb (x 0 13)
    have b11272 := hb (x (-1) 1 && x (-1) 14)
    clear * - r11269 b11270 b11271 b11272 d11256 g1
    omega
  have d11273 : (x (-1) 14).toNat = 1 := by
    have r11274 := hand2 (x (-1) 1) (x (-1) 14)
    have b11275 := hb (x (-1) 14)
    have b11276 := hb (x (-1) 1 && x (-1) 14)
    clear * - r11274 b11275 b11276 d11268
    omega
  have d11277 : (x (-2) 1).toNat = 0 := by
    have r11278 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11279 := hb (x (-2) 1)
    have b11280 := hb (x (-1) 14)
    clear * - r11278 b11279 b11280 d11273
    omega
  have d11281 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
    have r11282 := hand1 (x (-2) 1) (x (-2) 14)
    have b11283 := hb (x (-2) 1)
    have b11284 := hb (x (-2) 1 && x (-2) 14)
    clear * - r11282 b11283 b11284 d11277
    omega
  have d11285 : (x (-2) 13).toNat = 0 := by
    have r11286 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
    have b11287 := hb (x (-2) 1)
    have b11288 := hb (x (-2) 13)
    clear * - r11286 b11287 b11288 d11277
    omega
  have d11289 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
    have r11290 := hand2 (x (-2) 3) (x (-2) 13)
    have b11291 := hb (x (-2) 13)
    have b11292 := hb (x (-2) 3 && x (-2) 13)
    clear * - r11290 b11291 b11292 d11285
    omega
  have d11293 : (x (-2) 9).toNat = 0 := by
    have r11294 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
    have b11295 := hb (x (-2) 1)
    have b11296 := hb (x (-2) 9)
    clear * - r11294 b11295 b11296 d11277
    omega
  have d11297 : (x (-1) 1).toNat = 1 := by
    have r11298 := hand1 (x (-1) 1) (x (-1) 14)
    have b11299 := hb (x (-1) 1)
    have b11300 := hb (x (-1) 1 && x (-1) 14)
    clear * - r11298 b11299 b11300 d11268
    omega
  have d11301 : (x 0 14).toNat = 0 := by
    have r11302 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11303 := hb (x (-1) 1)
    have b11304 := hb (x 0 14)
    clear * - r11302 b11303 b11304 d11297
    omega
  have d11305 : (x 0 4 && x 0 14).toNat = 0 := by
    have r11306 := hand2 (x 0 4) (x 0 14)
    have b11307 := hb (x 0 14)
    have b11308 := hb (x 0 4 && x 0 14)
    clear * - r11306 b11307 b11308 d11301
    omega
  have d11309 : (x 0 7 && x 0 14).toNat = 0 := by
    have r11310 := hand2 (x 0 7) (x 0 14)
    have b11311 := hb (x 0 14)
    have b11312 := hb (x 0 7 && x 0 14)
    clear * - r11310 b11311 b11312 d11301
    omega
  have d11313 : (x 0 6).toNat = 0 := by
    have r11314 : (x 0 6).toNat ≤ (x 0 14).toNat := himp _ _ (hp6 0)
    have b11315 := hb (x 0 6)
    have b11316 := hb (x 0 14)
    clear * - r11314 b11315 b11316 d11301
    omega
  have d11317 : (x 0 2).toNat = 0 := by
    have r11318 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
    have b11319 := hb (x 0 2)
    have b11320 := hb (x 0 14)
    clear * - r11318 b11319 b11320 d11301
    omega
  have d11321 : (x 1 1 && x 1 14).toNat = 1 := by
    have r11322 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11323 := hb (x 0 2)
    have b11324 := hb (x 2 13)
    have b11325 := hb (x 1 1 && x 1 14)
    clear * - r11322 b11323 b11324 b11325 g11 d11317
    omega
  have d11326 : (x 1 1).toNat = 1 := by
    have r11327 := hand1 (x 1 1) (x 1 14)
    have b11328 := hb (x 1 1)
    have b11329 := hb (x 1 1 && x 1 14)
    clear * - r11327 b11328 b11329 d11321
    omega
  have d11330 : (x 2 14).toNat = 0 := by
    have r11331 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11332 := hb (x 1 1)
    have b11333 := hb (x 2 14)
    clear * - r11331 b11332 b11333 d11326
    omega
  have d11334 : (x 2 1 && x 2 14).toNat = 0 := by
    have r11335 := hand2 (x 2 1) (x 2 14)
    have b11336 := hb (x 2 14)
    have b11337 := hb (x 2 1 && x 2 14)
    clear * - r11335 b11336 b11337 d11330
    omega
  have d11338 : (x 3 13).toNat = 1 := by
    have r11339 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11340 := hb (x 1 2)
    have b11341 := hb (x 3 13)
    have b11342 := hb (x 2 1 && x 2 14)
    clear * - r11339 b11340 b11341 b11342 d11334 g8
    omega
  have d11343 : (x 3 1).toNat = 1 := by
    have r11344 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b11345 := hb (x 3 1)
    have b11346 := hb (x 3 13)
    clear * - r11344 b11345 b11346 d11338
    omega
  have d11347 : (x 4 14).toNat = 0 := by
    have r11348 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11349 := hb (x 3 1)
    have b11350 := hb (x 4 14)
    clear * - r11348 b11349 b11350 d11343
    omega
  have d11351 : (x 4 1 && x 4 14).toNat = 0 := by
    have r11352 := hand2 (x 4 1) (x 4 14)
    have b11353 := hb (x 4 14)
    have b11354 := hb (x 4 1 && x 4 14)
    clear * - r11352 b11353 b11354 d11347
    omega
  have d11355 : (x 4 3 && x 4 14).toNat = 0 := by
    have r11356 := hand2 (x 4 3) (x 4 14)
    have b11357 := hb (x 4 14)
    have b11358 := hb (x 4 3 && x 4 14)
    clear * - r11356 b11357 b11358 d11347
    omega
  have d11359 : (x 4 2).toNat = 0 := by
    have r11360 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
    have b11361 := hb (x 4 2)
    have b11362 := hb (x 4 14)
    clear * - r11360 b11361 b11362 d11347
    omega
  have d11363 : (x 4 10).toNat = 0 := by
    have r11364 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
    have b11365 := hb (x 4 2)
    have b11366 := hb (x 4 10)
    clear * - r11364 b11365 b11366 d11359
    omega
  have d11367 : (x 4 3 && x 4 10).toNat = 0 := by
    have r11368 := hand2 (x 4 3) (x 4 10)
    have b11369 := hb (x 4 10)
    have b11370 := hb (x 4 3 && x 4 10)
    clear * - r11368 b11369 b11370 d11363
    omega
  have d11371 : (x 2 2).toNat = 0 := by
    have r11372 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
    have b11373 := hb (x 2 2)
    have b11374 := hb (x 2 14)
    clear * - r11372 b11373 b11374 d11330
    omega
  have d11375 : (x 2 2 && x 2 12).toNat = 0 := by
    have r11376 := hand1 (x 2 2) (x 2 12)
    have b11377 := hb (x 2 2)
    have b11378 := hb (x 2 2 && x 2 12)
    clear * - r11376 b11377 b11378 d11371
    omega
  have d11379 : (x (-3) 2).toNat = 1 := by
    have r11380 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11381 := hb (x (-3) 2)
    have b11382 := hb (x (-1) 13)
    have b11383 := hb (x (-2) 1 && x (-2) 14)
    clear * - r11380 b11381 b11382 b11383 g5 d11281
    omega
  have d11384 : (x (-3) 14).toNat = 1 := by
    have r11385 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
    have b11386 := hb (x (-3) 2)
    have b11387 := hb (x (-3) 14)
    clear * - r11385 b11386 b11387 d11379
    omega
  have d11388 : (x (-4) 1).toNat = 0 := by
    have r11389 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11390 := hb (x (-4) 1)
    have b11391 := hb (x (-3) 14)
    clear * - r11389 b11390 b11391 d11384
    omega
  have d11392 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
    have r11393 := hand1 (x (-4) 1) (x (-4) 14)
    have b11394 := hb (x (-4) 1)
    have b11395 := hb (x (-4) 1 && x (-4) 14)
    clear * - r11393 b11394 b11395 d11388
    omega
  have d11396 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
    have r11397 := hand1 (x (-4) 1) (x (-4) 12)
    have b11398 := hb (x (-4) 1)
    have b11399 := hb (x (-4) 1 && x (-4) 12)
    clear * - r11397 b11398 b11399 d11388
    omega
  have d11400 : (x (-4) 1 && x (-4) 11).toNat = 0 := by
    have r11401 := hand1 (x (-4) 1) (x (-4) 11)
    have b11402 := hb (x (-4) 1)
    have b11403 := hb (x (-4) 1 && x (-4) 11)
    clear * - r11401 b11402 b11403 d11388
    omega
  have d11404 : (x (-4) 13).toNat = 0 := by
    have r11405 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
    have b11406 := hb (x (-4) 1)
    have b11407 := hb (x (-4) 13)
    clear * - r11405 b11406 b11407 d11388
    omega
  have d11408 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
    have r11409 := hand2 (x (-4) 4) (x (-4) 13)
    have b11410 := hb (x (-4) 13)
    have b11411 := hb (x (-4) 4 && x (-4) 13)
    clear * - r11409 b11410 b11411 d11404
    omega
  have d11412 : (x (-4) 5).toNat = 0 := by
    have r11413 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
    have b11414 := hb (x (-4) 5)
    have b11415 := hb (x (-4) 13)
    clear * - r11413 b11414 b11415 d11404
    omega
  have d11416 : (x (-4) 9).toNat = 0 := by
    have r11417 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
    have b11418 := hb (x (-4) 1)
    have b11419 := hb (x (-4) 9)
    clear * - r11417 b11418 b11419 d11388
    omega
  have d11420 : (x 4 12).toNat = 0 := by
    have r11421 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11422 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e11423 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b11424 := hb (x 1 3)
    have b11425 := hb (x 2 2)
    have b11426 := hb (x 3 13)
    have b11427 := hb (x 4 12)
    clear * - r11421 e11422 e11423 b11424 b11425 b11426 b11427 d11338 d11371
    omega
  have d11428 : (x 1 3).toNat = 0 := by
    have r11429 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11430 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e11431 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b11432 := hb (x 1 3)
    have b11433 := hb (x 2 2)
    have b11434 := hb (x 3 13)
    have b11435 := hb (x 4 12)
    clear * - r11429 e11430 e11431 b11432 b11433 b11434 b11435 d11420 d11338 d11371
    omega
  have d11436 : (x 1 3 && x 1 13).toNat = 0 := by
    have r11437 := hand1 (x 1 3) (x 1 13)
    have b11438 := hb (x 1 3)
    have b11439 := hb (x 1 3 && x 1 13)
    clear * - r11437 b11438 b11439 d11428
    omega
  have d11440 : (x (-1) 12).toNat = 0 := by
    have r11441 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11442 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e11443 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b11444 := hb (x (-4) 3)
    have b11445 := hb (x (-3) 2)
    have b11446 := hb (x (-2) 13)
    have b11447 := hb (x (-1) 12)
    clear * - r11441 e11442 e11443 b11444 b11445 b11446 b11447 d11285 d11379
    omega
  have d11448 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
    have r11449 := hand2 (x (-1) 2) (x (-1) 12)
    have b11450 := hb (x (-1) 12)
    have b11451 := hb (x (-1) 2 && x (-1) 12)
    clear * - r11449 b11450 b11451 d11440
    omega
  have d11452 : (x (-4) 3).toNat = 0 := by
    have r11453 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11454 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
    have e11455 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
    have b11456 := hb (x (-4) 3)
    have b11457 := hb (x (-3) 2)
    have b11458 := hb (x (-2) 13)
    have b11459 := hb (x (-1) 12)
    clear * - r11453 e11454 e11455 b11456 b11457 b11458 b11459 d11440 d11285 d11379
    omega
  have d11460 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
    have r11461 := hand1 (x (-4) 3) (x (-4) 12)
    have b11462 := hb (x (-4) 3)
    have b11463 := hb (x (-4) 3 && x (-4) 12)
    clear * - r11461 b11462 b11463 d11452
    omega
  have d11464 : (x (-4) 11).toNat = 0 := by
    have r11465 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
    have b11466 := hb (x (-4) 3)
    have b11467 := hb (x (-4) 11)
    clear * - r11465 b11466 b11467 d11452
    omega
  have d11468 : (x 3 1 && x 3 11).toNat = 1 := by
    have r11469 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11470 := hb (x (-1) 5)
    have b11471 := hb (x 4 10)
    have b11472 := hb (x 3 1 && x 3 11)
    have b11473 := hb (x 2 2 && x 2 12)
    have b11474 := hb (x 1 3 && x 1 13)
    have b11475 := hb (x 0 4 && x 0 14)
    clear * - r11469 b11470 b11471 b11472 b11473 b11474 b11475 d11363 d11375 d11436 d11305 g4
    omega
  have d11476 : (x 3 11).toNat = 1 := by
    have r11477 := hand2 (x 3 1) (x 3 11)
    have b11478 := hb (x 3 11)
    have b11479 := hb (x 3 1 && x 3 11)
    clear * - r11477 b11478 b11479 d11468
    omega
  have d11480 : (x 3 3).toNat = 1 := by
    have r11481 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b11482 := hb (x 3 3)
    have b11483 := hb (x 3 11)
    clear * - r11481 b11482 b11483 d11476
    omega
  have d11484 : (x 6 12).toNat = 0 := by
    have r11485 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11486 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e11487 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b11488 := hb (x 3 3)
    have b11489 := hb (x 4 2)
    have b11490 := hb (x 5 13)
    have b11491 := hb (x 6 12)
    clear * - r11485 e11486 e11487 b11488 b11489 b11490 b11491 d11359 d11480
    omega
  have d11492 : (x 6 1 && x 6 12).toNat = 0 := by
    have r11493 := hand2 (x 6 1) (x 6 12)
    have b11494 := hb (x 6 12)
    have b11495 := hb (x 6 1 && x 6 12)
    clear * - r11493 b11494 b11495 d11484
    omega
  have d11496 : (x 6 4).toNat = 0 := by
    have r11497 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
    have b11498 := hb (x 6 4)
    have b11499 := hb (x 6 12)
    clear * - r11497 b11498 b11499 d11484
    omega
  have d11500 : (x 6 4 && x 6 14).toNat = 0 := by
    have r11501 := hand1 (x 6 4) (x 6 14)
    have b11502 := hb (x 6 4)
    have b11503 := hb (x 6 4 && x 6 14)
    clear * - r11501 b11502 b11503 d11496
    omega
  have d11504 : (x 5 13).toNat = 0 := by
    have r11505 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11506 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e11507 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b11508 := hb (x 3 3)
    have b11509 := hb (x 4 2)
    have b11510 := hb (x 5 13)
    have b11511 := hb (x 6 12)
    clear * - r11505 e11506 e11507 b11508 b11509 b11510 b11511 d11484 d11359 d11480
    omega
  have d11512 : (x 5 2 && x 5 13).toNat = 0 := by
    have r11513 := hand2 (x 5 2) (x 5 13)
    have b11514 := hb (x 5 13)
    have b11515 := hb (x 5 2 && x 5 13)
    clear * - r11513 b11514 b11515 d11504
    omega
  have d11516 : (x 7 11).toNat = 1 := by
    have r11517 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11518 := hb (x 3 4)
    have b11519 := hb (x 7 11)
    have b11520 := hb (x 6 1 && x 6 12)
    have b11521 := hb (x 5 2 && x 5 13)
    have b11522 := hb (x 4 3 && x 4 14)
    clear * - r11517 b11518 b11519 b11520 b11521 b11522 d11492 d11512 d11355 g12
    omega
  have d11523 : (x 7 3).toNat = 1 := by
    have r11524 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b11525 := hb (x 7 3)
    have b11526 := hb (x 7 11)
    clear * - r11524 b11525 b11526 d11516
    omega
  have d11527 : (x 10 12).toNat = 0 := by
    have r11528 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11529 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e11530 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b11531 := hb (x 7 3)
    have b11532 := hb (x 8 2)
    have b11533 := hb (x 9 13)
    have b11534 := hb (x 10 12)
    clear * - r11528 e11529 e11530 b11531 b11532 b11533 b11534 d11523
    omega
  have d11535 : (x 10 1 && x 10 12).toNat = 0 := by
    have r11536 := hand2 (x 10 1) (x 10 12)
    have b11537 := hb (x 10 12)
    have b11538 := hb (x 10 1 && x 10 12)
    clear * - r11536 b11537 b11538 d11527
    omega
  have d11539 : (x 10 4).toNat = 0 := by
    have r11540 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
    have b11541 := hb (x 10 4)
    have b11542 := hb (x 10 12)
    clear * - r11540 b11541 b11542 d11527
    omega
  have d11543 : (x 9 13).toNat = 0 := by
    have r11544 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11545 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e11546 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b11547 := hb (x 7 3)
    have b11548 := hb (x 8 2)
    have b11549 := hb (x 9 13)
    have b11550 := hb (x 10 12)
    clear * - r11544 e11545 e11546 b11547 b11548 b11549 b11550 d11527 d11523
    omega
  have d11551 : (x 9 2 && x 9 13).toNat = 0 := by
    have r11552 := hand2 (x 9 2) (x 9 13)
    have b11553 := hb (x 9 13)
    have b11554 := hb (x 9 2 && x 9 13)
    clear * - r11552 b11553 b11554 d11543
    omega
  have d11555 : (x 9 5).toNat = 0 := by
    have r11556 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
    have b11557 := hb (x 9 5)
    have b11558 := hb (x 9 13)
    clear * - r11556 b11557 b11558 d11543
    omega
  have d11559 : (x 8 2).toNat = 0 := by
    have r11560 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11561 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e11562 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b11563 := hb (x 7 3)
    have b11564 := hb (x 8 2)
    have b11565 := hb (x 9 13)
    have b11566 := hb (x 10 12)
    clear * - r11560 e11561 e11562 b11563 b11564 b11565 b11566 d11527 d11543 d11523
    omega
  have d11567 : (x 8 2 && x 8 12).toNat = 0 := by
    have r11568 := hand1 (x 8 2) (x 8 12)
    have b11569 := hb (x 8 2)
    have b11570 := hb (x 8 2 && x 8 12)
    clear * - r11568 b11569 b11570 d11559
    omega
  have d11571 : (x 5 5).toNat = 0 := by
    have r11572 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
    have b11573 := hb (x 5 5)
    have b11574 := hb (x 5 13)
    clear * - r11572 b11573 b11574 d11504
    omega
  have d11575 : (x 3 2).toNat = 1 := by
    have r11576 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11577 := hb (x 3 2)
    have b11578 := hb (x 5 13)
    have b11579 := hb (x 4 1 && x 4 14)
    clear * - r11576 b11577 b11578 b11579 d11504 d11351
    omega
  have d11580 : (x 3 14).toNat = 1 := by
    have r11581 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b11582 := hb (x 3 2)
    have b11583 := hb (x 3 14)
    clear * - r11581 b11582 b11583 d11575
    omega
  have d11584 : (x 2 1).toNat = 0 := by
    have r11585 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11586 := hb (x 2 1)
    have b11587 := hb (x 3 14)
    clear * - r11585 b11586 b11587 d11580
    omega
  have d11588 : (x 2 1 && x 2 11).toNat = 0 := by
    have r11589 := hand1 (x 2 1) (x 2 11)
    have b11590 := hb (x 2 1)
    have b11591 := hb (x 2 1 && x 2 11)
    clear * - r11589 b11590 b11591 d11584
    omega
  have d11592 : (x 5 12).toNat = 0 := by
    have r11593 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11594 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e11595 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b11596 := hb (x 2 3)
    have b11597 := hb (x 3 2)
    have b11598 := hb (x 4 13)
    have b11599 := hb (x 5 12)
    clear * - r11593 e11594 e11595 b11596 b11597 b11598 b11599 d11575
    omega
  have d11600 : (x 4 13).toNat = 0 := by
    have r11601 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11602 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e11603 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b11604 := hb (x 2 3)
    have b11605 := hb (x 3 2)
    have b11606 := hb (x 4 13)
    have b11607 := hb (x 5 12)
    clear * - r11601 e11602 e11603 b11604 b11605 b11606 b11607 d11592 d11575
    omega
  have d11608 : (x 2 3).toNat = 0 := by
    have r11609 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11610 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e11611 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b11612 := hb (x 2 3)
    have b11613 := hb (x 3 2)
    have b11614 := hb (x 4 13)
    have b11615 := hb (x 5 12)
    clear * - r11609 e11610 e11611 b11612 b11613 b11614 b11615 d11592 d11600 d11575
    omega
  have d11616 : (x 2 11).toNat = 0 := by
    have r11617 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
    have b11618 := hb (x 2 3)
    have b11619 := hb (x 2 11)
    clear * - r11617 b11618 b11619 d11608
    omega
  have d11620 : (x 3 10).toNat = 1 := by
    have r11621 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11622 := hb (x (-2) 5)
    have b11623 := hb (x 3 10)
    have b11624 := hb (x 2 1 && x 2 11)
    have b11625 := hb (x 1 2 && x 1 12)
    have b11626 := hb (x 0 3 && x 0 13)
    have b11627 := hb (x (-1) 4 && x (-1) 14)
    clear * - r11621 b11622 b11623 b11624 b11625 b11626 b11627 d11588 g25 d11260 g26 g2
    omega
  have d11628 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
    have r11629 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11630 := hb (x (-4) 5)
    have b11631 := hb (x 1 10)
    have b11632 := hb (x 0 1 && x 0 11)
    have b11633 := hb (x (-1) 2 && x (-1) 12)
    have b11634 := hb (x (-2) 3 && x (-2) 13)
    have b11635 := hb (x (-3) 4 && x (-3) 14)
    clear * - r11629 b11630 b11631 b11632 b11633 b11634 b11635 g9 d11252 d11448 d11289 d11412
    omega
  have d11636 : (x (-3) 4).toNat = 1 := by
    have r11637 := hand1 (x (-3) 4) (x (-3) 14)
    have b11638 := hb (x (-3) 4)
    have b11639 := hb (x (-3) 4 && x (-3) 14)
    clear * - r11637 b11638 b11639 d11628
    omega
  have d11640 : (x (-3) 12).toNat = 1 := by
    have r11641 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
    have b11642 := hb (x (-3) 4)
    have b11643 := hb (x (-3) 12)
    clear * - r11641 b11642 b11643 d11636
    omega
  have d11644 : (x (-5) 2).toNat = 0 := by
    have r11645 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11646 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e11647 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b11648 := hb (x (-6) 3)
    have b11649 := hb (x (-5) 2)
    have b11650 := hb (x (-4) 13)
    have b11651 := hb (x (-3) 12)
    clear * - r11645 e11646 e11647 b11648 b11649 b11650 b11651 d11640 d11404
    omega
  have d11652 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
    have r11653 := hand1 (x (-5) 2) (x (-5) 13)
    have b11654 := hb (x (-5) 2)
    have b11655 := hb (x (-5) 2 && x (-5) 13)
    clear * - r11653 b11654 b11655 d11644
    omega
  have d11656 : (x (-5) 2 && x (-5) 12).toNat = 0 := by
    have r11657 := hand1 (x (-5) 2) (x (-5) 12)
    have b11658 := hb (x (-5) 2)
    have b11659 := hb (x (-5) 2 && x (-5) 12)
    clear * - r11657 b11658 b11659 d11644
    omega
  have d11660 : (x (-5) 10).toNat = 0 := by
    have r11661 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
    have b11662 := hb (x (-5) 2)
    have b11663 := hb (x (-5) 10)
    clear * - r11661 b11662 b11663 d11644
    omega
  have d11664 : (x (-3) 13).toNat = 1 := by
    have r11665 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11666 := hb (x (-5) 2)
    have b11667 := hb (x (-3) 13)
    have b11668 := hb (x (-4) 1 && x (-4) 14)
    clear * - r11665 b11666 b11667 b11668 d11392 d11644
    omega
  have d11669 : (x (-3) 1).toNat = 1 := by
    have r11670 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b11671 := hb (x (-3) 1)
    have b11672 := hb (x (-3) 13)
    clear * - r11670 b11671 b11672 d11664
    omega
  have d11673 : (x (-2) 14).toNat = 0 := by
    have r11674 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11675 := hb (x (-3) 1)
    have b11676 := hb (x (-2) 14)
    clear * - r11674 b11675 b11676 d11669
    omega
  have d11677 : (x (-2) 7 && x (-2) 14).toNat = 0 := by
    have r11678 := hand2 (x (-2) 7) (x (-2) 14)
    have b11679 := hb (x (-2) 14)
    have b11680 := hb (x (-2) 7 && x (-2) 14)
    clear * - r11678 b11679 b11680 d11673
    omega
  have d11681 : (x (-6) 3).toNat = 0 := by
    have r11682 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11683 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
    have e11684 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
    have b11685 := hb (x (-6) 3)
    have b11686 := hb (x (-5) 2)
    have b11687 := hb (x (-4) 13)
    have b11688 := hb (x (-3) 12)
    clear * - r11682 e11683 e11684 b11685 b11686 b11687 b11688 d11640 d11404 d11644
    omega
  have d11689 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
    have r11690 := hand1 (x (-6) 3) (x (-6) 14)
    have b11691 := hb (x (-6) 3)
    have b11692 := hb (x (-6) 3 && x (-6) 14)
    clear * - r11690 b11691 b11692 d11681
    omega
  have d11693 : (x (-7) 4).toNat = 1 := by
    have r11694 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11695 := hb (x (-7) 4)
    have b11696 := hb (x (-3) 11)
    have b11697 := hb (x (-4) 1 && x (-4) 12)
    have b11698 := hb (x (-5) 2 && x (-5) 13)
    have b11699 := hb (x (-6) 3 && x (-6) 14)
    clear * - r11694 b11695 b11696 b11697 b11698 b11699 g0 d11396 d11652 d11689
    omega
  have d11700 : (x (-7) 12).toNat = 1 := by
    have r11701 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
    have b11702 := hb (x (-7) 4)
    have b11703 := hb (x (-7) 12)
    clear * - r11701 b11702 b11703 d11693
    omega
  have d11704 : (x (-8) 13).toNat = 0 := by
    have r11705 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11706 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
    have e11707 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
    have b11708 := hb (x (-10) 3)
    have b11709 := hb (x (-9) 2)
    have b11710 := hb (x (-8) 13)
    have b11711 := hb (x (-7) 12)
    clear * - r11705 e11706 e11707 b11708 b11709 b11710 b11711 d11700
    omega
  have d11712 : (x (-8) 5).toNat = 0 := by
    have r11713 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
    have b11714 := hb (x (-8) 5)
    have b11715 := hb (x (-8) 13)
    clear * - r11713 b11714 b11715 d11704
    omega
  have d11716 : (x (-9) 2).toNat = 0 := by
    have r11717 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11718 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
    have e11719 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
    have b11720 := hb (x (-10) 3)
    have b11721 := hb (x (-9) 2)
    have b11722 := hb (x (-8) 13)
    have b11723 := hb (x (-7) 12)
    clear * - r11717 e11718 e11719 b11720 b11721 b11722 b11723 d11700 d11704
    omega
  have d11724 : (x (-6) 3 && x (-6) 13).toNat = 0 := by
    have r11725 := hand1 (x (-6) 3) (x (-6) 13)
    have b11726 := hb (x (-6) 3)
    have b11727 := hb (x (-6) 3 && x (-6) 13)
    clear * - r11725 b11726 b11727 d11681
    omega
  have d11728 : (x (-6) 11).toNat = 0 := by
    have r11729 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
    have b11730 := hb (x (-6) 3)
    have b11731 := hb (x (-6) 11)
    clear * - r11729 b11730 b11731 d11681
    omega
  have d11732 : (x 6 8).toNat = 0 := by
    have r11733 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11734 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e11735 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e11736 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e11737 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e11738 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e11739 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b11740 := hb (x (-1) 7)
    have b11741 := hb (x 0 6)
    have b11742 := hb (x 1 5)
    have b11743 := hb (x 2 4)
    have b11744 := hb (x 3 11)
    have b11745 := hb (x 4 10)
    have b11746 := hb (x 5 9)
    have b11747 := hb (x 6 8)
    clear * - r11733 e11734 e11735 e11736 e11737 e11738 e11739 b11740 b11741 b11742 b11743 b11744 b11745 b11746 b11747 d11363 d11476 d11313
    omega
  have d11748 : (x 6 1 && x 6 8).toNat = 0 := by
    have r11749 := hand2 (x 6 1) (x 6 8)
    have b11750 := hb (x 6 8)
    have b11751 := hb (x 6 1 && x 6 8)
    clear * - r11749 b11750 b11751 d11732
    omega
  have d11752 : (x 5 9).toNat = 0 := by
    have r11753 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11754 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e11755 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e11756 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e11757 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e11758 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e11759 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b11760 := hb (x (-1) 7)
    have b11761 := hb (x 0 6)
    have b11762 := hb (x 1 5)
    have b11763 := hb (x 2 4)
    have b11764 := hb (x 3 11)
    have b11765 := hb (x 4 10)
    have b11766 := hb (x 5 9)
    have b11767 := hb (x 6 8)
    clear * - r11753 e11754 e11755 e11756 e11757 e11758 e11759 b11760 b11761 b11762 b11763 b11764 b11765 b11766 b11767 d11732 d11363 d11476 d11313
    omega
  have d11768 : (x 5 2 && x 5 9).toNat = 0 := by
    have r11769 := hand2 (x 5 2) (x 5 9)
    have b11770 := hb (x 5 9)
    have b11771 := hb (x 5 2 && x 5 9)
    clear * - r11769 b11770 b11771 d11752
    omega
  have d11772 : (x 5 8).toNat = 0 := by
    have r11773 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11774 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e11775 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e11776 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e11777 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e11778 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e11779 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b11780 := hb (x (-2) 7)
    have b11781 := hb (x (-1) 6)
    have b11782 := hb (x 0 5)
    have b11783 := hb (x 1 4)
    have b11784 := hb (x 2 11)
    have b11785 := hb (x 3 10)
    have b11786 := hb (x 4 9)
    have b11787 := hb (x 5 8)
    clear * - r11773 e11774 e11775 e11776 e11777 e11778 e11779 b11780 b11781 b11782 b11783 b11784 b11785 b11786 b11787 d11620 d11616 g7
    omega
  have d11788 : (x 4 9).toNat = 0 := by
    have r11789 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11790 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e11791 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e11792 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e11793 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e11794 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e11795 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b11796 := hb (x (-2) 7)
    have b11797 := hb (x (-1) 6)
    have b11798 := hb (x 0 5)
    have b11799 := hb (x 1 4)
    have b11800 := hb (x 2 11)
    have b11801 := hb (x 3 10)
    have b11802 := hb (x 4 9)
    have b11803 := hb (x 5 8)
    clear * - r11789 e11790 e11791 e11792 e11793 e11794 e11795 b11796 b11797 b11798 b11799 b11800 b11801 b11802 b11803 d11772 d11620 d11616 g7
    omega
  have d11804 : (x 1 4).toNat = 0 := by
    have r11805 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11806 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
    have e11807 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
    have e11808 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
    have e11809 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
    have e11810 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
    have e11811 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
    have b11812 := hb (x (-2) 7)
    have b11813 := hb (x (-1) 6)
    have b11814 := hb (x 0 5)
    have b11815 := hb (x 1 4)
    have b11816 := hb (x 2 11)
    have b11817 := hb (x 3 10)
    have b11818 := hb (x 4 9)
    have b11819 := hb (x 5 8)
    clear * - r11805 e11806 e11807 e11808 e11809 e11810 e11811 b11812 b11813 b11814 b11815 b11816 b11817 b11818 b11819 d11772 d11788 d11620 d11616 g7
    omega
  have d11820 : (x 1 4 && x 1 14).toNat = 0 := by
    have r11821 := hand1 (x 1 4) (x 1 14)
    have b11822 := hb (x 1 4)
    have b11823 := hb (x 1 4 && x 1 14)
    clear * - r11821 b11822 b11823 d11804
    omega
  have d11824 : (x 1 8).toNat = 0 := by
    have r11825 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11826 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e11827 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e11828 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e11829 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e11830 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e11831 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b11832 := hb (x (-6) 7)
    have b11833 := hb (x (-5) 6)
    have b11834 := hb (x (-4) 5)
    have b11835 := hb (x (-3) 4)
    have b11836 := hb (x (-2) 11)
    have b11837 := hb (x (-1) 10)
    have b11838 := hb (x 0 9)
    have b11839 := hb (x 1 8)
    clear * - r11825 e11826 e11827 e11828 e11829 e11830 e11831 b11832 b11833 b11834 b11835 b11836 b11837 b11838 b11839 d11264 d11636 d11412
    omega
  have d11840 : (x (-1) 10).toNat = 0 := by
    have r11841 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11842 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
    have e11843 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
    have e11844 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
    have e11845 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
    have e11846 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
    have e11847 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
    have b11848 := hb (x (-6) 7)
    have b11849 := hb (x (-5) 6)
    have b11850 := hb (x (-4) 5)
    have b11851 := hb (x (-3) 4)
    have b11852 := hb (x (-2) 11)
    have b11853 := hb (x (-1) 10)
    have b11854 := hb (x 0 9)
    have b11855 := hb (x 1 8)
    clear * - r11841 e11842 e11843 e11844 e11845 e11846 e11847 b11848 b11849 b11850 b11851 b11852 b11853 b11854 b11855 d11824 d11264 d11636 d11412
    omega
  have d11856 : (x (-1) 1 && x (-1) 10).toNat = 0 := by
    have r11857 := hand2 (x (-1) 1) (x (-1) 10)
    have b11858 := hb (x (-1) 10)
    have b11859 := hb (x (-1) 1 && x (-1) 10)
    clear * - r11857 b11858 b11859 d11840
    omega
  have d11860 : (x (-3) 8).toNat = 0 := by
    have r11861 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11862 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
    have e11863 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
    have e11864 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
    have e11865 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
    have e11866 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
    have e11867 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
    have b11868 := hb (x (-10) 7)
    have b11869 := hb (x (-9) 6)
    have b11870 := hb (x (-8) 5)
    have b11871 := hb (x (-7) 4)
    have b11872 := hb (x (-6) 11)
    have b11873 := hb (x (-5) 10)
    have b11874 := hb (x (-4) 9)
    have b11875 := hb (x (-3) 8)
    clear * - r11861 e11862 e11863 e11864 e11865 e11866 e11867 b11868 b11869 b11870 b11871 b11872 b11873 b11874 b11875 d11416 d11660 d11728 d11693 d11712
    omega
  have d11876 : (x 5 7).toNat = 1 := by
    have r11877 : 1 ≤ (x 5 7).toNat + (x 4 1 && x 4 8).toNat + (x 3 2 && x 3 9).toNat + (x 2 3 && x 2 10).toNat + (x 1 4 && x 1 11).toNat + (x 0 5 && x 0 12).toNat + (x (-1) 6 && x (-1) 13).toNat + (x (-2) 7 && x (-2) 14).toNat + (x (-3) 8).toNat := by have q := hcov7 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11878 := hb (x (-3) 8)
    have b11879 := hb (x 5 7)
    have b11880 := hb (x 4 1 && x 4 8)
    have b11881 := hb (x 3 2 && x 3 9)
    have b11882 := hb (x 2 3 && x 2 10)
    have b11883 := hb (x 1 4 && x 1 11)
    have b11884 := hb (x 0 5 && x 0 12)
    have b11885 := hb (x (-1) 6 && x (-1) 13)
    have b11886 := hb (x (-2) 7 && x (-2) 14)
    clear * - r11877 b11878 b11879 b11880 b11881 b11882 b11883 b11884 b11885 b11886 g13 g14 g15 g16 g17 g18 d11677 d11860
    omega
  have d11887 : (x 12 8).toNat = 0 := by
    have r11888 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11889 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e11890 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e11891 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e11892 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e11893 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e11894 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b11895 := hb (x 5 7)
    have b11896 := hb (x 6 6)
    have b11897 := hb (x 7 5)
    have b11898 := hb (x 8 4)
    have b11899 := hb (x 9 11)
    have b11900 := hb (x 10 10)
    have b11901 := hb (x 11 9)
    have b11902 := hb (x 12 8)
    clear * - r11888 e11889 e11890 e11891 e11892 e11893 e11894 b11895 b11896 b11897 b11898 b11899 b11900 b11901 b11902 d11876
    omega
  have d11903 : (x 11 9).toNat = 0 := by
    have r11904 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11905 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e11906 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e11907 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e11908 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e11909 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e11910 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b11911 := hb (x 5 7)
    have b11912 := hb (x 6 6)
    have b11913 := hb (x 7 5)
    have b11914 := hb (x 8 4)
    have b11915 := hb (x 9 11)
    have b11916 := hb (x 10 10)
    have b11917 := hb (x 11 9)
    have b11918 := hb (x 12 8)
    clear * - r11904 e11905 e11906 e11907 e11908 e11909 e11910 b11911 b11912 b11913 b11914 b11915 b11916 b11917 b11918 d11887 d11876
    omega
  have d11919 : (x 10 10).toNat = 0 := by
    have r11920 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11921 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e11922 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e11923 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e11924 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e11925 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e11926 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b11927 := hb (x 5 7)
    have b11928 := hb (x 6 6)
    have b11929 := hb (x 7 5)
    have b11930 := hb (x 8 4)
    have b11931 := hb (x 9 11)
    have b11932 := hb (x 10 10)
    have b11933 := hb (x 11 9)
    have b11934 := hb (x 12 8)
    clear * - r11920 e11921 e11922 e11923 e11924 e11925 e11926 b11927 b11928 b11929 b11930 b11931 b11932 b11933 b11934 d11887 d11903 d11876
    omega
  have d11935 : (x 9 11).toNat = 0 := by
    have r11936 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e11937 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e11938 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e11939 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e11940 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e11941 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e11942 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have b11943 := hb (x 5 7)
    have b11944 := hb (x 6 6)
    have b11945 := hb (x 7 5)
    have b11946 := hb (x 8 4)
    have b11947 := hb (x 9 11)
    have b11948 := hb (x 10 10)
    have b11949 := hb (x 11 9)
    have b11950 := hb (x 12 8)
    clear * - r11936 e11937 e11938 e11939 e11940 e11941 e11942 b11943 b11944 b11945 b11946 b11947 b11948 b11949 b11950 d11887 d11903 d11919 d11876
    omega
  have d11951 : (x 9 1 && x 9 11).toNat = 0 := by
    have r11952 := hand2 (x 9 1) (x 9 11)
    have b11953 := hb (x 9 11)
    have b11954 := hb (x 9 1 && x 9 11)
    clear * - r11952 b11953 b11954 d11935
    omega
  have d11955 : (x 7 3 && x 7 13).toNat = 1 := by
    have r11956 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11957 := hb (x 5 5)
    have b11958 := hb (x 10 10)
    have b11959 := hb (x 9 1 && x 9 11)
    have b11960 := hb (x 8 2 && x 8 12)
    have b11961 := hb (x 7 3 && x 7 13)
    have b11962 := hb (x 6 4 && x 6 14)
    clear * - r11956 b11957 b11958 b11959 b11960 b11961 b11962 d11919 d11951 d11567 d11500 d11571
    omega
  have d11963 : (x 7 13).toNat = 1 := by
    have r11964 := hand2 (x 7 3) (x 7 13)
    have b11965 := hb (x 7 13)
    have b11966 := hb (x 7 3 && x 7 13)
    clear * - r11964 b11965 b11966 d11955
    omega
  have d11967 : (x 7 1).toNat = 1 := by
    have r11968 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b11969 := hb (x 7 1)
    have b11970 := hb (x 7 13)
    clear * - r11968 b11969 b11970 d11963
    omega
  have d11971 : (x 8 14).toNat = 0 := by
    have r11972 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11973 := hb (x 7 1)
    have b11974 := hb (x 8 14)
    clear * - r11972 b11973 b11974 d11967
    omega
  have d11975 : (x 8 1 && x 8 14).toNat = 0 := by
    have r11976 := hand2 (x 8 1) (x 8 14)
    have b11977 := hb (x 8 14)
    have b11978 := hb (x 8 1 && x 8 14)
    clear * - r11976 b11977 b11978 d11971
    omega
  have d11979 : (x 7 2).toNat = 1 := by
    have r11980 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11981 := hb (x 7 2)
    have b11982 := hb (x 9 13)
    have b11983 := hb (x 8 1 && x 8 14)
    clear * - r11980 b11981 b11982 b11983 d11543 d11975
    omega
  have d11984 : (x 7 14).toNat = 1 := by
    have r11985 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b11986 := hb (x 7 2)
    have b11987 := hb (x 7 14)
    clear * - r11985 b11986 b11987 d11979
    omega
  have d11988 : (x 6 1).toNat = 0 := by
    have r11989 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11990 := hb (x 6 1)
    have b11991 := hb (x 7 14)
    clear * - r11989 b11990 b11991 d11984
    omega
  have d11992 : (x 6 13).toNat = 0 := by
    have r11993 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b11994 := hb (x 6 1)
    have b11995 := hb (x 6 13)
    clear * - r11993 b11994 b11995 d11988
    omega
  have d11996 : (x 5 1 && x 5 14).toNat = 1 := by
    have r11997 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b11998 := hb (x 4 2)
    have b11999 := hb (x 6 13)
    have b12000 := hb (x 5 1 && x 5 14)
    clear * - r11997 b11998 b11999 b12000 d11992 d11359
    omega
  have d12001 : (x 5 14).toNat = 1 := by
    have r12002 := hand2 (x 5 1) (x 5 14)
    have b12003 := hb (x 5 14)
    have b12004 := hb (x 5 1 && x 5 14)
    clear * - r12002 b12003 b12004 d11996
    omega
  have d12005 : (x 4 1).toNat = 0 := by
    have r12006 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12007 := hb (x 4 1)
    have b12008 := hb (x 5 14)
    clear * - r12006 b12007 b12008 d12001
    omega
  have d12009 : (x 4 1 && x 4 11).toNat = 0 := by
    have r12010 := hand1 (x 4 1) (x 4 11)
    have b12011 := hb (x 4 1)
    have b12012 := hb (x 4 1 && x 4 11)
    clear * - r12010 b12011 b12012 d12005
    omega
  have d12013 : (x 5 10).toNat = 1 := by
    have r12014 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12015 := hb (x 0 5)
    have b12016 := hb (x 5 10)
    have b12017 := hb (x 4 1 && x 4 11)
    have b12018 := hb (x 3 2 && x 3 12)
    have b12019 := hb (x 2 3 && x 2 13)
    have b12020 := hb (x 1 4 && x 1 14)
    clear * - r12014 b12015 b12016 b12017 b12018 b12019 b12020 d12009 g27 g28 d11820 g7
    omega
  have d12021 : (x 5 2).toNat = 1 := by
    have r12022 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
    have b12023 := hb (x 5 2)
    have b12024 := hb (x 5 10)
    clear * - r12022 b12023 b12024 d12013
    omega
  have d12025 : (x 7 8).toNat = 0 := by
    have r12026 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12027 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e12028 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e12029 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e12030 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e12031 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e12032 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b12033 := hb (x 0 7)
    have b12034 := hb (x 1 6)
    have b12035 := hb (x 2 5)
    have b12036 := hb (x 3 4)
    have b12037 := hb (x 4 11)
    have b12038 := hb (x 5 10)
    have b12039 := hb (x 6 9)
    have b12040 := hb (x 7 8)
    clear * - r12026 e12027 e12028 e12029 e12030 e12031 e12032 b12033 b12034 b12035 b12036 b12037 b12038 b12039 b12040 d12013 g12 g10
    omega
  have d12041 : (x 6 9).toNat = 0 := by
    have r12042 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12043 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e12044 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e12045 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e12046 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e12047 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e12048 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b12049 := hb (x 0 7)
    have b12050 := hb (x 1 6)
    have b12051 := hb (x 2 5)
    have b12052 := hb (x 3 4)
    have b12053 := hb (x 4 11)
    have b12054 := hb (x 5 10)
    have b12055 := hb (x 6 9)
    have b12056 := hb (x 7 8)
    clear * - r12042 e12043 e12044 e12045 e12046 e12047 e12048 b12049 b12050 b12051 b12052 b12053 b12054 b12055 b12056 d12025 d12013 g12 g10
    omega
  have d12057 : (x 4 11).toNat = 0 := by
    have r12058 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12059 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e12060 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e12061 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e12062 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e12063 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e12064 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b12065 := hb (x 0 7)
    have b12066 := hb (x 1 6)
    have b12067 := hb (x 2 5)
    have b12068 := hb (x 3 4)
    have b12069 := hb (x 4 11)
    have b12070 := hb (x 5 10)
    have b12071 := hb (x 6 9)
    have b12072 := hb (x 7 8)
    clear * - r12058 e12059 e12060 e12061 e12062 e12063 e12064 b12065 b12066 b12067 b12068 b12069 b12070 b12071 b12072 d12025 d12041 d12013 g12 g10
    omega
  have d12073 : (x 1 6).toNat = 0 := by
    have r12074 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12075 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e12076 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e12077 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e12078 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e12079 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e12080 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b12081 := hb (x 0 7)
    have b12082 := hb (x 1 6)
    have b12083 := hb (x 2 5)
    have b12084 := hb (x 3 4)
    have b12085 := hb (x 4 11)
    have b12086 := hb (x 5 10)
    have b12087 := hb (x 6 9)
    have b12088 := hb (x 7 8)
    clear * - r12074 e12075 e12076 e12077 e12078 e12079 e12080 b12081 b12082 b12083 b12084 b12085 b12086 b12087 b12088 d12025 d12041 d12013 d12057 g12 g10
    omega
  have d12089 : (x 1 6 && x 1 13).toNat = 0 := by
    have r12090 := hand1 (x 1 6) (x 1 13)
    have b12091 := hb (x 1 6)
    have b12092 := hb (x 1 6 && x 1 13)
    clear * - r12090 b12091 b12092 d12073
    omega
  have d12093 : (x 7 12).toNat = 0 := by
    have r12094 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12095 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e12096 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b12097 := hb (x 4 3)
    have b12098 := hb (x 5 2)
    have b12099 := hb (x 6 13)
    have b12100 := hb (x 7 12)
    clear * - r12094 e12095 e12096 b12097 b12098 b12099 b12100 d11992 d12021
    omega
  have d12101 : (x 7 4).toNat = 0 := by
    have r12102 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b12103 := hb (x 7 4)
    have b12104 := hb (x 7 12)
    clear * - r12102 b12103 b12104 d12093
    omega
  have d12105 : (x 8 3 && x 8 14).toNat = 0 := by
    have r12106 := hand2 (x 8 3) (x 8 14)
    have b12107 := hb (x 8 14)
    have b12108 := hb (x 8 3 && x 8 14)
    clear * - r12106 b12107 b12108 d11971
    omega
  have d12109 : (x 11 11).toNat = 1 := by
    have r12110 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12111 := hb (x 7 4)
    have b12112 := hb (x 11 11)
    have b12113 := hb (x 10 1 && x 10 12)
    have b12114 := hb (x 9 2 && x 9 13)
    have b12115 := hb (x 8 3 && x 8 14)
    clear * - r12110 b12111 b12112 b12113 b12114 b12115 d11535 d11551 d12105 d12101
    omega
  have d12116 : (x 11 3).toNat = 1 := by
    have r12117 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
    have b12118 := hb (x 11 3)
    have b12119 := hb (x 11 11)
    clear * - r12117 b12118 b12119 d12109
    omega
  have d12120 : (x 14 12).toNat = 0 := by
    have r12121 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12122 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e12123 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b12124 := hb (x 11 3)
    have b12125 := hb (x 12 2)
    have b12126 := hb (x 13 13)
    have b12127 := hb (x 14 12)
    clear * - r12121 e12122 e12123 b12124 b12125 b12126 b12127 d12116
    omega
  have d12128 : (x 13 13).toNat = 0 := by
    have r12129 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12130 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e12131 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b12132 := hb (x 11 3)
    have b12133 := hb (x 12 2)
    have b12134 := hb (x 13 13)
    have b12135 := hb (x 14 12)
    clear * - r12129 e12130 e12131 b12132 b12133 b12134 b12135 d12120 d12116
    omega
  have d12136 : (x 12 2).toNat = 0 := by
    have r12137 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12138 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e12139 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b12140 := hb (x 11 3)
    have b12141 := hb (x 12 2)
    have b12142 := hb (x 13 13)
    have b12143 := hb (x 14 12)
    clear * - r12137 e12138 e12139 b12140 b12141 b12142 b12143 d12120 d12128 d12116
    omega
  have d12144 : (x 12 10).toNat = 0 := by
    have r12145 : (x 12 10).toNat ≤ (x 12 2).toNat := himp _ _ (hp10 12)
    have b12146 := hb (x 12 2)
    have b12147 := hb (x 12 10)
    clear * - r12145 b12146 b12147 d12136
    omega
  have d12148 : (x 14 8).toNat = 0 := by
    have r12149 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12150 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e12151 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e12152 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e12153 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e12154 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e12155 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b12156 := hb (x 7 7)
    have b12157 := hb (x 8 6)
    have b12158 := hb (x 9 5)
    have b12159 := hb (x 10 4)
    have b12160 := hb (x 11 11)
    have b12161 := hb (x 12 10)
    have b12162 := hb (x 13 9)
    have b12163 := hb (x 14 8)
    clear * - r12149 e12150 e12151 e12152 e12153 e12154 e12155 b12156 b12157 b12158 b12159 b12160 b12161 b12162 b12163 d12144 d12109 d11539 d11555
    omega
  have d12164 : (x 13 9).toNat = 0 := by
    have r12165 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12166 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e12167 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e12168 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e12169 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e12170 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e12171 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b12172 := hb (x 7 7)
    have b12173 := hb (x 8 6)
    have b12174 := hb (x 9 5)
    have b12175 := hb (x 10 4)
    have b12176 := hb (x 11 11)
    have b12177 := hb (x 12 10)
    have b12178 := hb (x 13 9)
    have b12179 := hb (x 14 8)
    clear * - r12165 e12166 e12167 e12168 e12169 e12170 e12171 b12172 b12173 b12174 b12175 b12176 b12177 b12178 b12179 d12148 d12144 d12109 d11539 d11555
    omega
  have d12180 : (x 8 6).toNat = 0 := by
    have r12181 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12182 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e12183 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e12184 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e12185 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e12186 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e12187 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b12188 := hb (x 7 7)
    have b12189 := hb (x 8 6)
    have b12190 := hb (x 9 5)
    have b12191 := hb (x 10 4)
    have b12192 := hb (x 11 11)
    have b12193 := hb (x 12 10)
    have b12194 := hb (x 13 9)
    have b12195 := hb (x 14 8)
    clear * - r12181 e12182 e12183 e12184 e12185 e12186 e12187 b12188 b12189 b12190 b12191 b12192 b12193 b12194 b12195 d12148 d12164 d12144 d12109 d11539 d11555
    omega
  have d12196 : (x 7 7).toNat = 0 := by
    have r12197 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12198 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e12199 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e12200 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e12201 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e12202 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e12203 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b12204 := hb (x 7 7)
    have b12205 := hb (x 8 6)
    have b12206 := hb (x 9 5)
    have b12207 := hb (x 10 4)
    have b12208 := hb (x 11 11)
    have b12209 := hb (x 12 10)
    have b12210 := hb (x 13 9)
    have b12211 := hb (x 14 8)
    clear * - r12197 e12198 e12199 e12200 e12201 e12202 e12203 b12204 b12205 b12206 b12207 b12208 b12209 b12210 b12211 d12148 d12164 d12144 d12109 d11539 d11555 d12180
    omega
  have d12212 : (x (-1) 8).toNat = 1 := by
    have r12213 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12214 := hb (x (-1) 8)
    have b12215 := hb (x 7 7)
    have b12216 := hb (x 6 1 && x 6 8)
    have b12217 := hb (x 5 2 && x 5 9)
    have b12218 := hb (x 4 3 && x 4 10)
    have b12219 := hb (x 3 4 && x 3 11)
    have b12220 := hb (x 2 5 && x 2 12)
    have b12221 := hb (x 1 6 && x 1 13)
    have b12222 := hb (x 0 7 && x 0 14)
    clear * - r12213 b12214 b12215 b12216 b12217 b12218 b12219 b12220 b12221 b12222 d12196 d11748 d11768 d11367 g19 g20 d12089 d11309
    omega
  have d12223 : (x (-3) 10).toNat = 0 := by
    have r12224 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12225 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e12226 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e12227 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e12228 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e12229 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e12230 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b12231 := hb (x (-8) 7)
    have b12232 := hb (x (-7) 6)
    have b12233 := hb (x (-6) 5)
    have b12234 := hb (x (-5) 4)
    have b12235 := hb (x (-4) 11)
    have b12236 := hb (x (-3) 10)
    have b12237 := hb (x (-2) 9)
    have b12238 := hb (x (-1) 8)
    clear * - r12224 e12225 e12226 e12227 e12228 e12229 e12230 b12231 b12232 b12233 b12234 b12235 b12236 b12237 b12238 d12212 d11293 d11464
    omega
  have d12239 : (x (-7) 4 && x (-7) 14).toNat = 1 := by
    have r12240 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := by have q := hcov10 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12241 := hb (x (-8) 5)
    have b12242 := hb (x (-3) 10)
    have b12243 := hb (x (-4) 1 && x (-4) 11)
    have b12244 := hb (x (-5) 2 && x (-5) 12)
    have b12245 := hb (x (-6) 3 && x (-6) 13)
    have b12246 := hb (x (-7) 4 && x (-7) 14)
    clear * - r12240 b12241 b12242 b12243 b12244 b12245 b12246 d12223 d11400 d11656 d11724 d11712
    omega
  have d12247 : (x (-7) 14).toNat = 1 := by
    have r12248 := hand2 (x (-7) 4) (x (-7) 14)
    have b12249 := hb (x (-7) 14)
    have b12250 := hb (x (-7) 4 && x (-7) 14)
    clear * - r12248 b12249 b12250 d12239
    omega
  have d12251 : (x (-8) 1).toNat = 0 := by
    have r12252 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12253 := hb (x (-8) 1)
    have b12254 := hb (x (-7) 14)
    clear * - r12252 b12253 b12254 d12247
    omega
  have d12255 : (x (-8) 1 && x (-8) 14).toNat = 0 := by
    have r12256 := hand1 (x (-8) 1) (x (-8) 14)
    have b12257 := hb (x (-8) 1)
    have b12258 := hb (x (-8) 1 && x (-8) 14)
    clear * - r12256 b12257 b12258 d12251
    omega
  have d12259 : (x (-7) 13).toNat = 1 := by
    have r12260 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := by have q := hcov13 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12261 := hb (x (-9) 2)
    have b12262 := hb (x (-7) 13)
    have b12263 := hb (x (-8) 1 && x (-8) 14)
    clear * - r12260 b12261 b12262 b12263 d12255 d11716
    omega
  have d12264 : (x (-7) 1).toNat = 1 := by
    have r12265 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
    have b12266 := hb (x (-7) 1)
    have b12267 := hb (x (-7) 13)
    clear * - r12265 b12266 b12267 d12259
    omega
  have d12268 : (x (-6) 14).toNat = 0 := by
    have r12269 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12270 := hb (x (-7) 1)
    have b12271 := hb (x (-6) 14)
    clear * - r12269 b12270 b12271 d12264
    omega
  have d12272 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
    have r12273 := hand2 (x (-6) 5) (x (-6) 14)
    have b12274 := hb (x (-6) 14)
    have b12275 := hb (x (-6) 5 && x (-6) 14)
    clear * - r12273 b12274 b12275 d12268
    omega
  have d12276 : (x (-6) 6).toNat = 0 := by
    have r12277 : (x (-6) 6).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp6 (-6))
    have b12278 := hb (x (-6) 6)
    have b12279 := hb (x (-6) 14)
    clear * - r12277 b12278 b12279 d12268
    omega
  have d12280 : (x (-5) 5 && x (-5) 14).toNat = 1 := by
    have r12281 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12282 := hb (x (-6) 6)
    have b12283 := hb (x 0 9)
    have b12284 := hb (x (-1) 1 && x (-1) 10)
    have b12285 := hb (x (-2) 2 && x (-2) 11)
    have b12286 := hb (x (-3) 3 && x (-3) 12)
    have b12287 := hb (x (-4) 4 && x (-4) 13)
    have b12288 := hb (x (-5) 5 && x (-5) 14)
    clear * - r12281 b12282 b12283 b12284 b12285 b12286 b12287 b12288 d11264 d11856 g23 g24 d11408 d12276
    omega
  have d12289 : (x (-5) 14).toNat = 1 := by
    have r12290 := hand2 (x (-5) 5) (x (-5) 14)
    have b12291 := hb (x (-5) 14)
    have b12292 := hb (x (-5) 5 && x (-5) 14)
    clear * - r12290 b12291 b12292 d12280
    omega
  have d12293 : (x (-6) 1).toNat = 0 := by
    have r12294 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12295 := hb (x (-6) 1)
    have b12296 := hb (x (-5) 14)
    clear * - r12294 b12295 b12296 d12289
    omega
  have d12297 : (x (-6) 13).toNat = 0 := by
    have r12298 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
    have b12299 := hb (x (-6) 1)
    have b12300 := hb (x (-6) 13)
    clear * - r12298 b12299 b12300 d12293
    omega
  have d12301 : (x (-6) 5).toNat = 0 := by
    have r12302 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
    have b12303 := hb (x (-6) 5)
    have b12304 := hb (x (-6) 13)
    clear * - r12302 b12303 b12304 d12297
    omega
  have d12305 : (x (-5) 5).toNat = 1 := by
    have r12306 := hand1 (x (-5) 5) (x (-5) 14)
    have b12307 := hb (x (-5) 5)
    have b12308 := hb (x (-5) 5 && x (-5) 14)
    clear * - r12306 b12307 b12308 d12280
    omega
  have d12309 : (x (-5) 13).toNat = 1 := by
    have r12310 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
    have b12311 := hb (x (-5) 5)
    have b12312 := hb (x (-5) 13)
    clear * - r12310 b12311 b12312 d12305
    omega
  have d12313 : (x (-4) 12).toNat = 0 := by
    have r12314 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12315 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
    have e12316 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
    have b12317 := hb (x (-7) 3)
    have b12318 := hb (x (-6) 2)
    have b12319 := hb (x (-5) 13)
    have b12320 := hb (x (-4) 12)
    clear * - r12314 e12315 e12316 b12317 b12318 b12319 b12320 d12309
    omega
  have d12321 : (x (-4) 4).toNat = 0 := by
    have r12322 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
    have b12323 := hb (x (-4) 4)
    have b12324 := hb (x (-4) 12)
    clear * - r12322 b12323 b12324 d12313
    omega
  have d12325 : (x 0 8).toNat = 0 := by
    have r12326 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12327 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e12328 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e12329 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e12330 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e12331 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e12332 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b12333 := hb (x (-7) 7)
    have b12334 := hb (x (-6) 6)
    have b12335 := hb (x (-5) 5)
    have b12336 := hb (x (-4) 4)
    have b12337 := hb (x (-3) 11)
    have b12338 := hb (x (-2) 10)
    have b12339 := hb (x (-1) 9)
    have b12340 := hb (x 0 8)
    clear * - r12326 e12327 e12328 e12329 e12330 e12331 e12332 b12333 b12334 b12335 b12336 b12337 b12338 b12339 b12340 g3 g0 d12321 d12305 d12276
    omega
  have d12341 : (x (-1) 9).toNat = 0 := by
    have r12342 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12343 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e12344 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e12345 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e12346 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e12347 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e12348 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b12349 := hb (x (-7) 7)
    have b12350 := hb (x (-6) 6)
    have b12351 := hb (x (-5) 5)
    have b12352 := hb (x (-4) 4)
    have b12353 := hb (x (-3) 11)
    have b12354 := hb (x (-2) 10)
    have b12355 := hb (x (-1) 9)
    have b12356 := hb (x 0 8)
    clear * - r12342 e12343 e12344 e12345 e12346 e12347 e12348 b12349 b12350 b12351 b12352 b12353 b12354 b12355 b12356 d12325 g3 g0 d12321 d12305 d12276
    omega
  have d12357 : (x (-5) 4).toNat = 0 := by
    have r12358 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e12359 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e12360 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e12361 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e12362 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e12363 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e12364 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have b12365 := hb (x (-8) 7)
    have b12366 := hb (x (-7) 6)
    have b12367 := hb (x (-6) 5)
    have b12368 := hb (x (-5) 4)
    have b12369 := hb (x (-4) 11)
    have b12370 := hb (x (-3) 10)
    have b12371 := hb (x (-2) 9)
    have b12372 := hb (x (-1) 8)
    clear * - r12358 e12359 e12360 e12361 e12362 e12363 e12364 b12365 b12366 b12367 b12368 b12369 b12370 b12371 b12372 d12212 d11293 d12223 d11464 d12301
    omega
  have d12373 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
    have r12374 := hand1 (x (-5) 4) (x (-5) 13)
    have b12375 := hb (x (-5) 4)
    have b12376 := hb (x (-5) 4 && x (-5) 13)
    clear * - r12374 b12375 b12376 d12357
    omega
  have d12377 : (x (-7) 6).toNat = 1 := by
    have r12378 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b12379 := hb (x (-7) 6)
    have b12380 := hb (x (-1) 9)
    have b12381 := hb (x (-2) 1 && x (-2) 10)
    have b12382 := hb (x (-3) 2 && x (-3) 11)
    have b12383 := hb (x (-4) 3 && x (-4) 12)
    have b12384 := hb (x (-5) 4 && x (-5) 13)
    have b12385 := hb (x (-6) 5 && x (-6) 14)
    clear * - r12378 b12379 b12380 b12381 b12382 b12383 b12384 b12385 d12341 g21 g22 d11460 d12373 d12272
    omega
  have r12386 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have e12387 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
  have e12388 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
  have e12389 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
  have e12390 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
  have e12391 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
  have e12392 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
  have b12393 := hb (x (-8) 7)
  have b12394 := hb (x (-7) 6)
  have b12395 := hb (x (-6) 5)
  have b12396 := hb (x (-5) 4)
  have b12397 := hb (x (-4) 11)
  have b12398 := hb (x (-3) 10)
  have b12399 := hb (x (-2) 9)
  have b12400 := hb (x (-1) 8)
  linarith only [r12386, e12387, e12388, e12389, e12390, e12391, e12392, b12393, b12394, b12395, b12396, b12397, b12398, b12399, b12400, d12212, d11293, d12223, d11464, d12357, d12301, d12377]

theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b010 (x : ℤ → Fin 16 → Bool)
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
    (g2 : (x (-2) 5).toNat = 0)
    (g3 : (x (-2) 10).toNat = 0)
    (g4 : (x (-1) 5).toNat = 0)
    (g5 : (x (-1) 13).toNat = 0)
    (g6 : (x 0 1).toNat = 0)
    (g7 : (x 0 5).toNat = 0)
    (g8 : (x 1 2).toNat = 0)
    (g9 : (x 1 10).toNat = 0)
    (g10 : (x 2 5).toNat = 0)
    (g11 : (x 2 13).toNat = 0)
    (g12 : (x 3 4).toNat = 0)
    (g13 : (x 4 1 && x 4 8).toNat = 0)
    (g14 : (x 3 2 && x 3 9).toNat = 0)
    (g15 : (x 2 3 && x 2 10).toNat = 0)
    (g16 : (x 1 4 && x 1 11).toNat = 0)
    (g17 : (x 0 5 && x 0 12).toNat = 0)
    (g18 : (x (-1) 6 && x (-1) 13).toNat = 0)
    (g19 : (x 3 4 && x 3 11).toNat = 0)
    (g20 : (x 2 5 && x 2 12).toNat = 0)
    (g21 : (x (-2) 1 && x (-2) 10).toNat = 0)
    (g22 : (x (-3) 2 && x (-3) 11).toNat = 0)
    (g23 : (x (-2) 2 && x (-2) 11).toNat = 0)
    (g24 : (x (-3) 3 && x (-3) 12).toNat = 0)
    (g25 : (x 1 2 && x 1 12).toNat = 0)
    (g26 : (x (-1) 4 && x (-1) 14).toNat = 0)
    (g27 : (x 3 2 && x 3 12).toNat = 0)
    (g28 : (x 2 3 && x 2 13).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b010_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28
