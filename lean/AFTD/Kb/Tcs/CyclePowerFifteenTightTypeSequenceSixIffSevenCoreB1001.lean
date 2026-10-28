import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b1001

Topic: combinatorics   Node: ef4f3bf3735a

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_six_iff_seven_core: under the layer-free tight-cover constraints for k = 15 and 17 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b1001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 2).toNat = 1)
    (g1 : (x 0 6).toNat = 0)
    (g2 : (x 0 13).toNat = 0)
    (g3 : (x 1 2).toNat = 0)
    (g4 : (x 2 5).toNat = 0)
    (g5 : (x 3 4).toNat = 0)
    (g6 : (x 4 11).toNat = 0)
    (g7 : (x 5 10).toNat = 0)
    (g8 : (x 6 9).toNat = 0)
    (g9 : (x 7 8).toNat = 0)
    (g10 : (x 7 8 && x 7 12).toNat = 0)
    (g11 : (x 6 9 && x 6 13).toNat = 0)
    (g12 : (x 5 1 && x 5 10).toNat = 0)
    (g13 : (x 4 2 && x 4 11).toNat = 0)
    (g14 : (x 1 5 && x 1 14).toNat = 0)
    (g15 : (x 3 4 && x 3 14).toNat = 0)
    (g16 : (x 1 3 && x 1 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d17256 : (x 0 14).toNat = 1 := by
    have r17257 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
    have b17258 := hb (x 0 2)
    have b17259 := hb (x 0 14)
    clear * - r17257 b17258 b17259 g0
    omega
  have d17260 : (x (-1) 1).toNat = 0 := by
    have r17261 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17262 := hb (x (-1) 1)
    have b17263 := hb (x 0 14)
    clear * - r17261 b17262 b17263 d17256
    omega
  have d17264 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
    have r17265 := hand1 (x (-1) 1) (x (-1) 14)
    have b17266 := hb (x (-1) 1)
    have b17267 := hb (x (-1) 1 && x (-1) 14)
    clear * - r17265 b17266 b17267 d17260
    omega
  have d17268 : (x (-1) 13).toNat = 0 := by
    have r17269 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b17270 := hb (x (-1) 1)
    have b17271 := hb (x (-1) 13)
    clear * - r17269 b17270 b17271 d17260
    omega
  have d17272 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
    have r17273 := hand2 (x (-1) 3) (x (-1) 13)
    have b17274 := hb (x (-1) 13)
    have b17275 := hb (x (-1) 3 && x (-1) 13)
    clear * - r17273 b17274 b17275 d17268
    omega
  have d17276 : (x (-1) 5).toNat = 0 := by
    have r17277 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b17278 := hb (x (-1) 5)
    have b17279 := hb (x (-1) 13)
    clear * - r17277 b17278 b17279 d17268
    omega
  have d17280 : (x (-2) 2).toNat = 1 := by
    have r17281 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17282 := hb (x (-2) 2)
    have b17283 := hb (x 0 13)
    have b17284 := hb (x (-1) 1 && x (-1) 14)
    clear * - r17281 b17282 b17283 b17284 g2 d17264
    omega
  have d17285 : (x (-2) 14).toNat = 1 := by
    have r17286 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
    have b17287 := hb (x (-2) 2)
    have b17288 := hb (x (-2) 14)
    clear * - r17286 b17287 b17288 d17280
    omega
  have d17289 : (x (-3) 1).toNat = 0 := by
    have r17290 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17291 := hb (x (-3) 1)
    have b17292 := hb (x (-2) 14)
    clear * - r17290 b17291 b17292 d17285
    omega
  have d17293 : (x (-3) 13).toNat = 0 := by
    have r17294 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b17295 := hb (x (-3) 1)
    have b17296 := hb (x (-3) 13)
    clear * - r17294 b17295 b17296 d17289
    omega
  have d17297 : (x (-3) 5).toNat = 0 := by
    have r17298 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
    have b17299 := hb (x (-3) 5)
    have b17300 := hb (x (-3) 13)
    clear * - r17298 b17299 b17300 d17293
    omega
  have d17301 : (x 2 12).toNat = 0 := by
    have r17302 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17303 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e17304 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b17305 := hb (x (-1) 3)
    have b17306 := hb (x 0 2)
    have b17307 := hb (x 1 13)
    have b17308 := hb (x 2 12)
    clear * - r17302 e17303 e17304 b17305 b17306 b17307 b17308 g0
    omega
  have d17309 : (x 2 2 && x 2 12).toNat = 0 := by
    have r17310 := hand2 (x 2 2) (x 2 12)
    have b17311 := hb (x 2 12)
    have b17312 := hb (x 2 2 && x 2 12)
    clear * - r17310 b17311 b17312 d17301
    omega
  have d17313 : (x 2 8 && x 2 12).toNat = 0 := by
    have r17314 := hand2 (x 2 8) (x 2 12)
    have b17315 := hb (x 2 12)
    have b17316 := hb (x 2 8 && x 2 12)
    clear * - r17314 b17315 b17316 d17301
    omega
  have d17317 : (x 2 4).toNat = 0 := by
    have r17318 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b17319 := hb (x 2 4)
    have b17320 := hb (x 2 12)
    clear * - r17318 b17319 b17320 d17301
    omega
  have d17321 : (x 2 4 && x 2 13).toNat = 0 := by
    have r17322 := hand1 (x 2 4) (x 2 13)
    have b17323 := hb (x 2 4)
    have b17324 := hb (x 2 4 && x 2 13)
    clear * - r17322 b17323 b17324 d17317
    omega
  have d17325 : (x 1 13).toNat = 0 := by
    have r17326 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17327 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e17328 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b17329 := hb (x (-1) 3)
    have b17330 := hb (x 0 2)
    have b17331 := hb (x 1 13)
    have b17332 := hb (x 2 12)
    clear * - r17326 e17327 e17328 b17329 b17330 b17331 b17332 d17301 g0
    omega
  have d17333 : (x 1 3 && x 1 13).toNat = 0 := by
    have r17334 := hand2 (x 1 3) (x 1 13)
    have b17335 := hb (x 1 13)
    have b17336 := hb (x 1 3 && x 1 13)
    clear * - r17334 b17335 b17336 d17325
    omega
  have d17337 : (x 1 9 && x 1 13).toNat = 0 := by
    have r17338 := hand2 (x 1 9) (x 1 13)
    have b17339 := hb (x 1 13)
    have b17340 := hb (x 1 9 && x 1 13)
    clear * - r17338 b17339 b17340 d17325
    omega
  have d17341 : (x 1 5).toNat = 0 := by
    have r17342 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b17343 := hb (x 1 5)
    have b17344 := hb (x 1 13)
    clear * - r17342 b17343 b17344 d17325
    omega
  have d17345 : (x (-1) 3).toNat = 0 := by
    have r17346 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17347 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e17348 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b17349 := hb (x (-1) 3)
    have b17350 := hb (x 0 2)
    have b17351 := hb (x 1 13)
    have b17352 := hb (x 2 12)
    clear * - r17346 e17347 e17348 b17349 b17350 b17351 b17352 d17301 d17325 g0
    omega
  have d17353 : (x (-1) 11).toNat = 0 := by
    have r17354 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b17355 := hb (x (-1) 3)
    have b17356 := hb (x (-1) 11)
    clear * - r17354 b17355 b17356 d17345
    omega
  have d17357 : (x 0 12).toNat = 0 := by
    have r17358 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17359 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e17360 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b17361 := hb (x (-3) 3)
    have b17362 := hb (x (-2) 2)
    have b17363 := hb (x (-1) 13)
    have b17364 := hb (x 0 12)
    clear * - r17358 e17359 e17360 b17361 b17362 b17363 b17364 d17268 d17280
    omega
  have d17365 : (x 0 2 && x 0 12).toNat = 0 := by
    have r17366 := hand2 (x 0 2) (x 0 12)
    have b17367 := hb (x 0 12)
    have b17368 := hb (x 0 2 && x 0 12)
    clear * - r17366 b17367 b17368 d17357
    omega
  have d17369 : (x 0 4).toNat = 0 := by
    have r17370 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b17371 := hb (x 0 4)
    have b17372 := hb (x 0 12)
    clear * - r17370 b17371 b17372 d17357
    omega
  have d17373 : (x 0 4 && x 0 14).toNat = 0 := by
    have r17374 := hand1 (x 0 4) (x 0 14)
    have b17375 := hb (x 0 4)
    have b17376 := hb (x 0 4 && x 0 14)
    clear * - r17374 b17375 b17376 d17369
    omega
  have d17377 : (x 3 3 && x 3 12).toNat = 1 := by
    have r17378 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17379 := hb (x 0 6)
    have b17380 := hb (x 6 9)
    have b17381 := hb (x 5 1 && x 5 10)
    have b17382 := hb (x 4 2 && x 4 11)
    have b17383 := hb (x 3 3 && x 3 12)
    have b17384 := hb (x 2 4 && x 2 13)
    have b17385 := hb (x 1 5 && x 1 14)
    clear * - r17378 b17379 b17380 b17381 b17382 b17383 b17384 b17385 g8 g12 g13 d17321 g14 g1
    omega
  have d17386 : (x 3 12).toNat = 1 := by
    have r17387 := hand2 (x 3 3) (x 3 12)
    have b17388 := hb (x 3 12)
    have b17389 := hb (x 3 3 && x 3 12)
    clear * - r17387 b17388 b17389 d17377
    omega
  have d17390 : (x 2 13).toNat = 0 := by
    have r17391 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17392 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e17393 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b17394 := hb (x 0 3)
    have b17395 := hb (x 1 2)
    have b17396 := hb (x 2 13)
    have b17397 := hb (x 3 12)
    clear * - r17391 e17392 e17393 b17394 b17395 b17396 b17397 d17386 g3
    omega
  have d17398 : (x 2 2 && x 2 13).toNat = 0 := by
    have r17399 := hand2 (x 2 2) (x 2 13)
    have b17400 := hb (x 2 13)
    have b17401 := hb (x 2 2 && x 2 13)
    clear * - r17399 b17400 b17401 d17390
    omega
  have d17402 : (x 3 1 && x 3 12).toNat = 1 := by
    have r17403 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17404 := hb (x 0 4)
    have b17405 := hb (x 4 11)
    have b17406 := hb (x 3 1 && x 3 12)
    have b17407 := hb (x 2 2 && x 2 13)
    have b17408 := hb (x 1 3 && x 1 14)
    clear * - r17403 b17404 b17405 b17406 b17407 b17408 g6 d17398 g16 d17369
    omega
  have d17409 : (x 3 1).toNat = 1 := by
    have r17410 := hand1 (x 3 1) (x 3 12)
    have b17411 := hb (x 3 1)
    have b17412 := hb (x 3 1 && x 3 12)
    clear * - r17410 b17411 b17412 d17402
    omega
  have d17413 : (x 4 14).toNat = 0 := by
    have r17414 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17415 := hb (x 3 1)
    have b17416 := hb (x 4 14)
    clear * - r17414 b17415 b17416 d17409
    omega
  have d17417 : (x 4 1 && x 4 14).toNat = 0 := by
    have r17418 := hand2 (x 4 1) (x 4 14)
    have b17419 := hb (x 4 14)
    have b17420 := hb (x 4 1 && x 4 14)
    clear * - r17418 b17419 b17420 d17413
    omega
  have d17421 : (x 4 3 && x 4 14).toNat = 0 := by
    have r17422 := hand2 (x 4 3) (x 4 14)
    have b17423 := hb (x 4 14)
    have b17424 := hb (x 4 3 && x 4 14)
    clear * - r17422 b17423 b17424 d17413
    omega
  have d17425 : (x 4 6).toNat = 0 := by
    have r17426 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
    have b17427 := hb (x 4 6)
    have b17428 := hb (x 4 14)
    clear * - r17426 b17427 b17428 d17413
    omega
  have d17429 : (x 4 6 && x 4 12).toNat = 0 := by
    have r17430 := hand1 (x 4 6) (x 4 12)
    have b17431 := hb (x 4 6)
    have b17432 := hb (x 4 6 && x 4 12)
    clear * - r17430 b17431 b17432 d17425
    omega
  have d17433 : (x 4 6 && x 4 10).toNat = 0 := by
    have r17434 := hand1 (x 4 6) (x 4 10)
    have b17435 := hb (x 4 6)
    have b17436 := hb (x 4 6 && x 4 10)
    clear * - r17434 b17435 b17436 d17425
    omega
  have d17437 : (x 4 2).toNat = 0 := by
    have r17438 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
    have b17439 := hb (x 4 2)
    have b17440 := hb (x 4 14)
    clear * - r17438 b17439 b17440 d17413
    omega
  have d17441 : (x 4 10).toNat = 0 := by
    have r17442 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
    have b17443 := hb (x 4 2)
    have b17444 := hb (x 4 10)
    clear * - r17442 b17443 b17444 d17437
    omega
  have d17445 : (x 3 1 && x 3 11).toNat = 1 := by
    have r17446 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17447 := hb (x (-1) 5)
    have b17448 := hb (x 4 10)
    have b17449 := hb (x 3 1 && x 3 11)
    have b17450 := hb (x 2 2 && x 2 12)
    have b17451 := hb (x 1 3 && x 1 13)
    have b17452 := hb (x 0 4 && x 0 14)
    clear * - r17446 b17447 b17448 b17449 b17450 b17451 b17452 d17441 d17309 d17333 d17373 d17276
    omega
  have d17453 : (x 3 11).toNat = 1 := by
    have r17454 := hand2 (x 3 1) (x 3 11)
    have b17455 := hb (x 3 11)
    have b17456 := hb (x 3 1 && x 3 11)
    clear * - r17454 b17455 b17456 d17445
    omega
  have d17457 : (x 3 3).toNat = 1 := by
    have r17458 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have b17459 := hb (x 3 3)
    have b17460 := hb (x 3 11)
    clear * - r17458 b17459 b17460 d17453
    omega
  have d17461 : (x 6 12).toNat = 0 := by
    have r17462 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17463 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e17464 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b17465 := hb (x 3 3)
    have b17466 := hb (x 4 2)
    have b17467 := hb (x 5 13)
    have b17468 := hb (x 6 12)
    clear * - r17462 e17463 e17464 b17465 b17466 b17467 b17468 d17437 d17457
    omega
  have d17469 : (x 6 1 && x 6 12).toNat = 0 := by
    have r17470 := hand2 (x 6 1) (x 6 12)
    have b17471 := hb (x 6 12)
    have b17472 := hb (x 6 1 && x 6 12)
    clear * - r17470 b17471 b17472 d17461
    omega
  have d17473 : (x 6 4).toNat = 0 := by
    have r17474 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
    have b17475 := hb (x 6 4)
    have b17476 := hb (x 6 12)
    clear * - r17474 b17475 b17476 d17461
    omega
  have d17477 : (x 6 4 && x 6 10).toNat = 0 := by
    have r17478 := hand1 (x 6 4) (x 6 10)
    have b17479 := hb (x 6 4)
    have b17480 := hb (x 6 4 && x 6 10)
    clear * - r17478 b17479 b17480 d17473
    omega
  have d17481 : (x 6 4 && x 6 8).toNat = 0 := by
    have r17482 := hand1 (x 6 4) (x 6 8)
    have b17483 := hb (x 6 4)
    have b17484 := hb (x 6 4 && x 6 8)
    clear * - r17482 b17483 b17484 d17473
    omega
  have d17485 : (x 5 13).toNat = 0 := by
    have r17486 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17487 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e17488 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have b17489 := hb (x 3 3)
    have b17490 := hb (x 4 2)
    have b17491 := hb (x 5 13)
    have b17492 := hb (x 6 12)
    clear * - r17486 e17487 e17488 b17489 b17490 b17491 b17492 d17461 d17437 d17457
    omega
  have d17493 : (x 5 2 && x 5 13).toNat = 0 := by
    have r17494 := hand2 (x 5 2) (x 5 13)
    have b17495 := hb (x 5 13)
    have b17496 := hb (x 5 2 && x 5 13)
    clear * - r17494 b17495 b17496 d17485
    omega
  have d17497 : (x 7 11).toNat = 1 := by
    have r17498 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17499 := hb (x 3 4)
    have b17500 := hb (x 7 11)
    have b17501 := hb (x 6 1 && x 6 12)
    have b17502 := hb (x 5 2 && x 5 13)
    have b17503 := hb (x 4 3 && x 4 14)
    clear * - r17498 b17499 b17500 b17501 b17502 b17503 d17469 d17493 d17421 g5
    omega
  have d17504 : (x 7 3).toNat = 1 := by
    have r17505 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b17506 := hb (x 7 3)
    have b17507 := hb (x 7 11)
    clear * - r17505 b17506 b17507 d17497
    omega
  have d17508 : (x 10 12).toNat = 0 := by
    have r17509 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17510 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e17511 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b17512 := hb (x 7 3)
    have b17513 := hb (x 8 2)
    have b17514 := hb (x 9 13)
    have b17515 := hb (x 10 12)
    clear * - r17509 e17510 e17511 b17512 b17513 b17514 b17515 d17504
    omega
  have d17516 : (x 10 3 && x 10 12).toNat = 0 := by
    have r17517 := hand2 (x 10 3) (x 10 12)
    have b17518 := hb (x 10 12)
    have b17519 := hb (x 10 3 && x 10 12)
    clear * - r17517 b17518 b17519 d17508
    omega
  have d17520 : (x 10 5 && x 10 12).toNat = 0 := by
    have r17521 := hand2 (x 10 5) (x 10 12)
    have b17522 := hb (x 10 12)
    have b17523 := hb (x 10 5 && x 10 12)
    clear * - r17521 b17522 b17523 d17508
    omega
  have d17524 : (x 10 4).toNat = 0 := by
    have r17525 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
    have b17526 := hb (x 10 4)
    have b17527 := hb (x 10 12)
    clear * - r17525 b17526 b17527 d17508
    omega
  have d17528 : (x 10 4 && x 10 14).toNat = 0 := by
    have r17529 := hand1 (x 10 4) (x 10 14)
    have b17530 := hb (x 10 4)
    have b17531 := hb (x 10 4 && x 10 14)
    clear * - r17529 b17530 b17531 d17524
    omega
  have d17532 : (x 9 13).toNat = 0 := by
    have r17533 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17534 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e17535 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b17536 := hb (x 7 3)
    have b17537 := hb (x 8 2)
    have b17538 := hb (x 9 13)
    have b17539 := hb (x 10 12)
    clear * - r17533 e17534 e17535 b17536 b17537 b17538 b17539 d17508 d17504
    omega
  have d17540 : (x 9 4 && x 9 13).toNat = 0 := by
    have r17541 := hand2 (x 9 4) (x 9 13)
    have b17542 := hb (x 9 13)
    have b17543 := hb (x 9 4 && x 9 13)
    clear * - r17541 b17542 b17543 d17532
    omega
  have d17544 : (x 9 6 && x 9 13).toNat = 0 := by
    have r17545 := hand2 (x 9 6) (x 9 13)
    have b17546 := hb (x 9 13)
    have b17547 := hb (x 9 6 && x 9 13)
    clear * - r17545 b17546 b17547 d17532
    omega
  have d17548 : (x 9 5).toNat = 0 := by
    have r17549 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
    have b17550 := hb (x 9 5)
    have b17551 := hb (x 9 13)
    clear * - r17549 b17550 b17551 d17532
    omega
  have d17552 : (x 8 2).toNat = 0 := by
    have r17553 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17554 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e17555 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b17556 := hb (x 7 3)
    have b17557 := hb (x 8 2)
    have b17558 := hb (x 9 13)
    have b17559 := hb (x 10 12)
    clear * - r17553 e17554 e17555 b17556 b17557 b17558 b17559 d17508 d17532 d17504
    omega
  have d17560 : (x 8 2 && x 8 8).toNat = 0 := by
    have r17561 := hand1 (x 8 2) (x 8 8)
    have b17562 := hb (x 8 2)
    have b17563 := hb (x 8 2 && x 8 8)
    clear * - r17561 b17562 b17563 d17552
    omega
  have d17564 : (x 8 2 && x 8 6).toNat = 0 := by
    have r17565 := hand1 (x 8 2) (x 8 6)
    have b17566 := hb (x 8 2)
    have b17567 := hb (x 8 2 && x 8 6)
    clear * - r17565 b17566 b17567 d17552
    omega
  have d17568 : (x 8 10).toNat = 0 := by
    have r17569 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
    have b17570 := hb (x 8 2)
    have b17571 := hb (x 8 10)
    clear * - r17569 b17570 b17571 d17552
    omega
  have d17572 : (x 5 5).toNat = 0 := by
    have r17573 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
    have b17574 := hb (x 5 5)
    have b17575 := hb (x 5 13)
    clear * - r17573 b17574 b17575 d17485
    omega
  have d17576 : (x 5 5 && x 5 11).toNat = 0 := by
    have r17577 := hand1 (x 5 5) (x 5 11)
    have b17578 := hb (x 5 5)
    have b17579 := hb (x 5 5 && x 5 11)
    clear * - r17577 b17578 b17579 d17572
    omega
  have d17580 : (x 5 5 && x 5 9).toNat = 0 := by
    have r17581 := hand1 (x 5 5) (x 5 9)
    have b17582 := hb (x 5 5)
    have b17583 := hb (x 5 5 && x 5 9)
    clear * - r17581 b17582 b17583 d17572
    omega
  have d17584 : (x 3 2).toNat = 1 := by
    have r17585 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17586 := hb (x 3 2)
    have b17587 := hb (x 5 13)
    have b17588 := hb (x 4 1 && x 4 14)
    clear * - r17585 b17586 b17587 b17588 d17485 d17417
    omega
  have d17589 : (x 3 14).toNat = 1 := by
    have r17590 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
    have b17591 := hb (x 3 2)
    have b17592 := hb (x 3 14)
    clear * - r17590 b17591 b17592 d17584
    omega
  have d17593 : (x 2 1).toNat = 0 := by
    have r17594 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17595 := hb (x 2 1)
    have b17596 := hb (x 3 14)
    clear * - r17594 b17595 b17596 d17589
    omega
  have d17597 : (x 2 1 && x 2 14).toNat = 0 := by
    have r17598 := hand1 (x 2 1) (x 2 14)
    have b17599 := hb (x 2 1)
    have b17600 := hb (x 2 1 && x 2 14)
    clear * - r17598 b17599 b17600 d17593
    omega
  have d17601 : (x 3 13).toNat = 1 := by
    have r17602 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17603 := hb (x 1 2)
    have b17604 := hb (x 3 13)
    have b17605 := hb (x 2 1 && x 2 14)
    clear * - r17602 b17603 b17604 b17605 d17597 g3
    omega
  have d17606 : (x 4 12).toNat = 0 := by
    have r17607 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17608 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e17609 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b17610 := hb (x 1 3)
    have b17611 := hb (x 2 2)
    have b17612 := hb (x 3 13)
    have b17613 := hb (x 4 12)
    clear * - r17607 e17608 e17609 b17610 b17611 b17612 b17613 d17601
    omega
  have d17614 : (x 2 2).toNat = 0 := by
    have r17615 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17616 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e17617 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b17618 := hb (x 1 3)
    have b17619 := hb (x 2 2)
    have b17620 := hb (x 3 13)
    have b17621 := hb (x 4 12)
    clear * - r17615 e17616 e17617 b17618 b17619 b17620 b17621 d17606 d17601
    omega
  have d17622 : (x 2 10).toNat = 0 := by
    have r17623 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
    have b17624 := hb (x 2 2)
    have b17625 := hb (x 2 10)
    clear * - r17623 b17624 b17625 d17614
    omega
  have d17626 : (x 1 3).toNat = 0 := by
    have r17627 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17628 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e17629 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b17630 := hb (x 1 3)
    have b17631 := hb (x 2 2)
    have b17632 := hb (x 3 13)
    have b17633 := hb (x 4 12)
    clear * - r17627 e17628 e17629 b17630 b17631 b17632 b17633 d17606 d17601 d17614
    omega
  have d17634 : (x 1 11).toNat = 0 := by
    have r17635 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have b17636 := hb (x 1 3)
    have b17637 := hb (x 1 11)
    clear * - r17635 b17636 b17637 d17626
    omega
  have d17638 : (x 1 1 && x 1 11).toNat = 0 := by
    have r17639 := hand2 (x 1 1) (x 1 11)
    have b17640 := hb (x 1 11)
    have b17641 := hb (x 1 1 && x 1 11)
    clear * - r17639 b17640 b17641 d17634
    omega
  have d17642 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
    have r17643 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17644 := hb (x (-3) 5)
    have b17645 := hb (x 2 10)
    have b17646 := hb (x 1 1 && x 1 11)
    have b17647 := hb (x 0 2 && x 0 12)
    have b17648 := hb (x (-1) 3 && x (-1) 13)
    have b17649 := hb (x (-2) 4 && x (-2) 14)
    clear * - r17643 b17644 b17645 b17646 b17647 b17648 b17649 d17622 d17638 d17365 d17272 d17297
    omega
  have d17650 : (x (-2) 4).toNat = 1 := by
    have r17651 := hand1 (x (-2) 4) (x (-2) 14)
    have b17652 := hb (x (-2) 4)
    have b17653 := hb (x (-2) 4 && x (-2) 14)
    clear * - r17651 b17652 b17653 d17642
    omega
  have d17654 : (x 5 12).toNat = 0 := by
    have r17655 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17656 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e17657 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b17658 := hb (x 2 3)
    have b17659 := hb (x 3 2)
    have b17660 := hb (x 4 13)
    have b17661 := hb (x 5 12)
    clear * - r17655 e17656 e17657 b17658 b17659 b17660 b17661 d17584
    omega
  have d17662 : (x 5 2 && x 5 12).toNat = 0 := by
    have r17663 := hand2 (x 5 2) (x 5 12)
    have b17664 := hb (x 5 12)
    have b17665 := hb (x 5 2 && x 5 12)
    clear * - r17663 b17664 b17665 d17654
    omega
  have d17666 : (x 5 4).toNat = 0 := by
    have r17667 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b17668 := hb (x 5 4)
    have b17669 := hb (x 5 12)
    clear * - r17667 b17668 b17669 d17654
    omega
  have d17670 : (x 4 13).toNat = 0 := by
    have r17671 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17672 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e17673 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b17674 := hb (x 2 3)
    have b17675 := hb (x 3 2)
    have b17676 := hb (x 4 13)
    have b17677 := hb (x 5 12)
    clear * - r17671 e17672 e17673 b17674 b17675 b17676 b17677 d17654 d17584
    omega
  have d17678 : (x 4 3 && x 4 13).toNat = 0 := by
    have r17679 := hand2 (x 4 3) (x 4 13)
    have b17680 := hb (x 4 13)
    have b17681 := hb (x 4 3 && x 4 13)
    clear * - r17679 b17680 b17681 d17670
    omega
  have d17682 : (x 4 5).toNat = 0 := by
    have r17683 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
    have b17684 := hb (x 4 5)
    have b17685 := hb (x 4 13)
    clear * - r17683 b17684 b17685 d17670
    omega
  have d17686 : (x 10 8).toNat = 0 := by
    have r17687 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17688 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e17689 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e17690 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e17691 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e17692 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e17693 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have b17694 := hb (x 3 7)
    have b17695 := hb (x 4 6)
    have b17696 := hb (x 5 5)
    have b17697 := hb (x 6 4)
    have b17698 := hb (x 7 11)
    have b17699 := hb (x 8 10)
    have b17700 := hb (x 9 9)
    have b17701 := hb (x 10 8)
    clear * - r17687 e17688 e17689 e17690 e17691 e17692 e17693 b17694 b17695 b17696 b17697 b17698 b17699 b17700 b17701 d17568 d17497 d17473 d17572 d17425
    omega
  have d17702 : (x 9 9).toNat = 0 := by
    have r17703 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17704 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e17705 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e17706 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e17707 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e17708 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e17709 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have b17710 := hb (x 3 7)
    have b17711 := hb (x 4 6)
    have b17712 := hb (x 5 5)
    have b17713 := hb (x 6 4)
    have b17714 := hb (x 7 11)
    have b17715 := hb (x 8 10)
    have b17716 := hb (x 9 9)
    have b17717 := hb (x 10 8)
    clear * - r17703 e17704 e17705 e17706 e17707 e17708 e17709 b17710 b17711 b17712 b17713 b17714 b17715 b17716 b17717 d17686 d17568 d17497 d17473 d17572 d17425
    omega
  have d17718 : (x 3 7).toNat = 0 := by
    have r17719 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17720 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
    have e17721 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
    have e17722 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
    have e17723 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
    have e17724 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
    have e17725 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
    have b17726 := hb (x 3 7)
    have b17727 := hb (x 4 6)
    have b17728 := hb (x 5 5)
    have b17729 := hb (x 6 4)
    have b17730 := hb (x 7 11)
    have b17731 := hb (x 8 10)
    have b17732 := hb (x 9 9)
    have b17733 := hb (x 10 8)
    clear * - r17719 e17720 e17721 e17722 e17723 e17724 e17725 b17726 b17727 b17728 b17729 b17730 b17731 b17732 b17733 d17686 d17702 d17568 d17497 d17473 d17572 d17425
    omega
  have d17734 : (x 3 7 && x 3 13).toNat = 0 := by
    have r17735 := hand1 (x 3 7) (x 3 13)
    have b17736 := hb (x 3 7)
    have b17737 := hb (x 3 7 && x 3 13)
    clear * - r17735 b17736 b17737 d17718
    omega
  have d17738 : (x 3 7 && x 3 11).toNat = 0 := by
    have r17739 := hand1 (x 3 7) (x 3 11)
    have b17740 := hb (x 3 7)
    have b17741 := hb (x 3 7 && x 3 11)
    clear * - r17739 b17740 b17741 d17718
    omega
  have d17742 : (x 6 8).toNat = 0 := by
    have r17743 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17744 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e17745 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e17746 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e17747 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e17748 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e17749 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b17750 := hb (x (-1) 7)
    have b17751 := hb (x 0 6)
    have b17752 := hb (x 1 5)
    have b17753 := hb (x 2 4)
    have b17754 := hb (x 3 11)
    have b17755 := hb (x 4 10)
    have b17756 := hb (x 5 9)
    have b17757 := hb (x 6 8)
    clear * - r17743 e17744 e17745 e17746 e17747 e17748 e17749 b17750 b17751 b17752 b17753 b17754 b17755 b17756 b17757 d17441 d17453 d17317 d17341 g1
    omega
  have d17758 : (x 5 9).toNat = 0 := by
    have r17759 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17760 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e17761 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e17762 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e17763 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e17764 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e17765 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b17766 := hb (x (-1) 7)
    have b17767 := hb (x 0 6)
    have b17768 := hb (x 1 5)
    have b17769 := hb (x 2 4)
    have b17770 := hb (x 3 11)
    have b17771 := hb (x 4 10)
    have b17772 := hb (x 5 9)
    have b17773 := hb (x 6 8)
    clear * - r17759 e17760 e17761 e17762 e17763 e17764 e17765 b17766 b17767 b17768 b17769 b17770 b17771 b17772 b17773 d17742 d17441 d17453 d17317 d17341 g1
    omega
  have d17774 : (x 2 8).toNat = 0 := by
    have r17775 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17776 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e17777 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e17778 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e17779 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e17780 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e17781 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b17782 := hb (x (-5) 7)
    have b17783 := hb (x (-4) 6)
    have b17784 := hb (x (-3) 5)
    have b17785 := hb (x (-2) 4)
    have b17786 := hb (x (-1) 11)
    have b17787 := hb (x 0 10)
    have b17788 := hb (x 1 9)
    have b17789 := hb (x 2 8)
    clear * - r17775 e17776 e17777 e17778 e17779 e17780 e17781 b17782 b17783 b17784 b17785 b17786 b17787 b17788 b17789 d17353 d17650 d17297
    omega
  have d17790 : (x 2 8 && x 2 14).toNat = 0 := by
    have r17791 := hand1 (x 2 8) (x 2 14)
    have b17792 := hb (x 2 8)
    have b17793 := hb (x 2 8 && x 2 14)
    clear * - r17791 b17792 b17793 d17774
    omega
  have d17794 : (x 1 9).toNat = 0 := by
    have r17795 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17796 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e17797 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e17798 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e17799 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e17800 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e17801 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b17802 := hb (x (-5) 7)
    have b17803 := hb (x (-4) 6)
    have b17804 := hb (x (-3) 5)
    have b17805 := hb (x (-2) 4)
    have b17806 := hb (x (-1) 11)
    have b17807 := hb (x 0 10)
    have b17808 := hb (x 1 9)
    have b17809 := hb (x 2 8)
    clear * - r17795 e17796 e17797 e17798 e17799 e17800 e17801 b17802 b17803 b17804 b17805 b17806 b17807 b17808 b17809 d17774 d17353 d17650 d17297
    omega
  have d17810 : (x 0 10).toNat = 0 := by
    have r17811 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17812 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
    have e17813 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
    have e17814 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
    have e17815 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
    have e17816 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
    have e17817 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
    have b17818 := hb (x (-5) 7)
    have b17819 := hb (x (-4) 6)
    have b17820 := hb (x (-3) 5)
    have b17821 := hb (x (-2) 4)
    have b17822 := hb (x (-1) 11)
    have b17823 := hb (x 0 10)
    have b17824 := hb (x 1 9)
    have b17825 := hb (x 2 8)
    clear * - r17811 e17812 e17813 e17814 e17815 e17816 e17817 b17818 b17819 b17820 b17821 b17822 b17823 b17824 b17825 d17774 d17794 d17353 d17650 d17297
    omega
  have d17826 : (x 7 3 && x 7 7).toNat = 1 := by
    have r17827 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17828 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
    have e17829 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
    have b17830 := hb (x (-1) 11)
    have b17831 := hb (x 0 10)
    have b17832 := hb (x 9 5)
    have b17833 := hb (x 10 4)
    have b17834 := hb (x 8 2 && x 8 6)
    have b17835 := hb (x 7 3 && x 7 7)
    have b17836 := hb (x 6 4 && x 6 8)
    have b17837 := hb (x 5 5 && x 5 9)
    have b17838 := hb (x 4 6 && x 4 10)
    have b17839 := hb (x 3 7 && x 3 11)
    have b17840 := hb (x 2 8 && x 2 12)
    have b17841 := hb (x 1 9 && x 1 13)
    clear * - r17827 e17828 e17829 b17830 b17831 b17832 b17833 b17834 b17835 b17836 b17837 b17838 b17839 b17840 b17841 d17524 d17548 d17564 d17481 d17580 d17433 d17738 d17313 d17337 d17810 d17353
    omega
  have d17842 : (x 7 7).toNat = 1 := by
    have r17843 := hand2 (x 7 3) (x 7 7)
    have b17844 := hb (x 7 7)
    have b17845 := hb (x 7 3 && x 7 7)
    clear * - r17843 b17844 b17845 d17826
    omega
  have d17846 : (x 14 8).toNat = 0 := by
    have r17847 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17848 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e17849 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e17850 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e17851 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e17852 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e17853 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b17854 := hb (x 7 7)
    have b17855 := hb (x 8 6)
    have b17856 := hb (x 9 5)
    have b17857 := hb (x 10 4)
    have b17858 := hb (x 11 11)
    have b17859 := hb (x 12 10)
    have b17860 := hb (x 13 9)
    have b17861 := hb (x 14 8)
    clear * - r17847 e17848 e17849 e17850 e17851 e17852 e17853 b17854 b17855 b17856 b17857 b17858 b17859 b17860 b17861 d17524 d17548 d17842
    omega
  have d17862 : (x 14 1 && x 14 8).toNat = 0 := by
    have r17863 := hand2 (x 14 1) (x 14 8)
    have b17864 := hb (x 14 8)
    have b17865 := hb (x 14 1 && x 14 8)
    clear * - r17863 b17864 b17865 d17846
    omega
  have d17866 : (x 13 9).toNat = 0 := by
    have r17867 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17868 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e17869 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e17870 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e17871 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e17872 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e17873 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b17874 := hb (x 7 7)
    have b17875 := hb (x 8 6)
    have b17876 := hb (x 9 5)
    have b17877 := hb (x 10 4)
    have b17878 := hb (x 11 11)
    have b17879 := hb (x 12 10)
    have b17880 := hb (x 13 9)
    have b17881 := hb (x 14 8)
    clear * - r17867 e17868 e17869 e17870 e17871 e17872 e17873 b17874 b17875 b17876 b17877 b17878 b17879 b17880 b17881 d17846 d17524 d17548 d17842
    omega
  have d17882 : (x 13 2 && x 13 9).toNat = 0 := by
    have r17883 := hand2 (x 13 2) (x 13 9)
    have b17884 := hb (x 13 9)
    have b17885 := hb (x 13 2 && x 13 9)
    clear * - r17883 b17884 b17885 d17866
    omega
  have d17886 : (x 12 10).toNat = 0 := by
    have r17887 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17888 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e17889 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e17890 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e17891 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e17892 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e17893 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b17894 := hb (x 7 7)
    have b17895 := hb (x 8 6)
    have b17896 := hb (x 9 5)
    have b17897 := hb (x 10 4)
    have b17898 := hb (x 11 11)
    have b17899 := hb (x 12 10)
    have b17900 := hb (x 13 9)
    have b17901 := hb (x 14 8)
    clear * - r17887 e17888 e17889 e17890 e17891 e17892 e17893 b17894 b17895 b17896 b17897 b17898 b17899 b17900 b17901 d17846 d17866 d17524 d17548 d17842
    omega
  have d17902 : (x 12 1 && x 12 10).toNat = 0 := by
    have r17903 := hand2 (x 12 1) (x 12 10)
    have b17904 := hb (x 12 10)
    have b17905 := hb (x 12 1 && x 12 10)
    clear * - r17903 b17904 b17905 d17886
    omega
  have d17906 : (x 12 3 && x 12 10).toNat = 0 := by
    have r17907 := hand2 (x 12 3) (x 12 10)
    have b17908 := hb (x 12 10)
    have b17909 := hb (x 12 3 && x 12 10)
    clear * - r17907 b17908 b17909 d17886
    omega
  have d17910 : (x 11 11).toNat = 0 := by
    have r17911 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17912 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e17913 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e17914 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e17915 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e17916 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e17917 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b17918 := hb (x 7 7)
    have b17919 := hb (x 8 6)
    have b17920 := hb (x 9 5)
    have b17921 := hb (x 10 4)
    have b17922 := hb (x 11 11)
    have b17923 := hb (x 12 10)
    have b17924 := hb (x 13 9)
    have b17925 := hb (x 14 8)
    clear * - r17911 e17912 e17913 e17914 e17915 e17916 e17917 b17918 b17919 b17920 b17921 b17922 b17923 b17924 b17925 d17846 d17866 d17886 d17524 d17548 d17842
    omega
  have d17926 : (x 11 2 && x 11 11).toNat = 0 := by
    have r17927 := hand2 (x 11 2) (x 11 11)
    have b17928 := hb (x 11 11)
    have b17929 := hb (x 11 2 && x 11 11)
    clear * - r17927 b17928 b17929 d17910
    omega
  have d17930 : (x 11 4 && x 11 11).toNat = 0 := by
    have r17931 := hand2 (x 11 4) (x 11 11)
    have b17932 := hb (x 11 11)
    have b17933 := hb (x 11 4 && x 11 11)
    clear * - r17931 b17932 b17933 d17910
    omega
  have d17934 : (x 8 6).toNat = 0 := by
    have r17935 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17936 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
    have e17937 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
    have e17938 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
    have e17939 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
    have e17940 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
    have e17941 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
    have b17942 := hb (x 7 7)
    have b17943 := hb (x 8 6)
    have b17944 := hb (x 9 5)
    have b17945 := hb (x 10 4)
    have b17946 := hb (x 11 11)
    have b17947 := hb (x 12 10)
    have b17948 := hb (x 13 9)
    have b17949 := hb (x 14 8)
    clear * - r17935 e17936 e17937 e17938 e17939 e17940 e17941 b17942 b17943 b17944 b17945 b17946 b17947 b17948 b17949 d17846 d17866 d17886 d17910 d17524 d17548 d17842
    omega
  have d17950 : (x 13 1).toNat = 0 := by
    have r17951 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17952 := hb (x 0 14)
    have b17953 := hb (x 1 13)
    have b17954 := hb (x 2 12)
    have b17955 := hb (x 3 11)
    have b17956 := hb (x 4 10)
    have b17957 := hb (x 5 9)
    have b17958 := hb (x 6 8)
    have b17959 := hb (x 7 7)
    have b17960 := hb (x 8 6)
    have b17961 := hb (x 9 5)
    have b17962 := hb (x 10 4)
    have b17963 := hb (x 11 3)
    have b17964 := hb (x 12 2)
    have b17965 := hb (x 13 1)
    clear * - r17951 b17952 b17953 b17954 b17955 b17956 b17957 b17958 b17959 b17960 b17961 b17962 b17963 b17964 b17965 d17524 d17548 d17934 d17842 d17742 d17758 d17441 d17453 d17301 d17325 d17256
    omega
  have d17966 : (x 13 1 && x 13 14).toNat = 0 := by
    have r17967 := hand1 (x 13 1) (x 13 14)
    have b17968 := hb (x 13 1)
    have b17969 := hb (x 13 1 && x 13 14)
    clear * - r17967 b17968 b17969 d17950
    omega
  have d17970 : (x 13 1 && x 13 12).toNat = 0 := by
    have r17971 := hand1 (x 13 1) (x 13 12)
    have b17972 := hb (x 13 1)
    have b17973 := hb (x 13 1 && x 13 12)
    clear * - r17971 b17972 b17973 d17950
    omega
  have d17974 : (x 13 1 && x 13 11).toNat = 0 := by
    have r17975 := hand1 (x 13 1) (x 13 11)
    have b17976 := hb (x 13 1)
    have b17977 := hb (x 13 1 && x 13 11)
    clear * - r17975 b17976 b17977 d17950
    omega
  have d17978 : (x 12 2).toNat = 0 := by
    have r17979 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17980 := hb (x 0 14)
    have b17981 := hb (x 1 13)
    have b17982 := hb (x 2 12)
    have b17983 := hb (x 3 11)
    have b17984 := hb (x 4 10)
    have b17985 := hb (x 5 9)
    have b17986 := hb (x 6 8)
    have b17987 := hb (x 7 7)
    have b17988 := hb (x 8 6)
    have b17989 := hb (x 9 5)
    have b17990 := hb (x 10 4)
    have b17991 := hb (x 11 3)
    have b17992 := hb (x 12 2)
    have b17993 := hb (x 13 1)
    clear * - r17979 b17980 b17981 b17982 b17983 b17984 b17985 b17986 b17987 b17988 b17989 b17990 b17991 b17992 b17993 d17950 d17524 d17548 d17934 d17842 d17742 d17758 d17441 d17453 d17301 d17325 d17256
    omega
  have d17994 : (x 12 2 && x 12 13).toNat = 0 := by
    have r17995 := hand1 (x 12 2) (x 12 13)
    have b17996 := hb (x 12 2)
    have b17997 := hb (x 12 2 && x 12 13)
    clear * - r17995 b17996 b17997 d17978
    omega
  have d17998 : (x 12 2 && x 12 12).toNat = 0 := by
    have r17999 := hand1 (x 12 2) (x 12 12)
    have b18000 := hb (x 12 2)
    have b18001 := hb (x 12 2 && x 12 12)
    clear * - r17999 b18000 b18001 d17978
    omega
  have d18002 : (x 14 13).toNat = 1 := by
    have r18003 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18004 := hb (x 12 2)
    have b18005 := hb (x 14 13)
    have b18006 := hb (x 13 1 && x 13 14)
    clear * - r18003 b18004 b18005 b18006 d17966 d17978
    omega
  have d18007 : (x 14 1).toNat = 1 := by
    have r18008 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
    have b18009 := hb (x 14 1)
    have b18010 := hb (x 14 13)
    clear * - r18008 b18009 b18010 d18002
    omega
  have d18011 : (x 15 14).toNat = 0 := by
    have r18012 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18013 := hb (x 14 1)
    have b18014 := hb (x 15 14)
    clear * - r18012 b18013 b18014 d18007
    omega
  have d18015 : (x 15 1 && x 15 14).toNat = 0 := by
    have r18016 := hand2 (x 15 1) (x 15 14)
    have b18017 := hb (x 15 14)
    have b18018 := hb (x 15 1 && x 15 14)
    clear * - r18016 b18017 b18018 d18011
    omega
  have d18019 : (x 15 2).toNat = 0 := by
    have r18020 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
    have b18021 := hb (x 15 2)
    have b18022 := hb (x 15 14)
    clear * - r18020 b18021 b18022 d18011
    omega
  have d18023 : (x 15 2 && x 15 8).toNat = 0 := by
    have r18024 := hand1 (x 15 2) (x 15 8)
    have b18025 := hb (x 15 2)
    have b18026 := hb (x 15 2 && x 15 8)
    clear * - r18024 b18025 b18026 d18019
    omega
  have d18027 : (x 15 10).toNat = 0 := by
    have r18028 : (x 15 10).toNat ≤ (x 15 2).toNat := himp _ _ (hp10 15)
    have b18029 := hb (x 15 2)
    have b18030 := hb (x 15 10)
    clear * - r18028 b18029 b18030 d18019
    omega
  have d18031 : (x 15 12).toNat = 0 := by
    have r18032 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18033 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e18034 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b18035 := hb (x 12 3)
    have b18036 := hb (x 13 2)
    have b18037 := hb (x 14 13)
    have b18038 := hb (x 15 12)
    clear * - r18032 e18033 e18034 b18035 b18036 b18037 b18038 d18002
    omega
  have d18039 : (x 15 4).toNat = 0 := by
    have r18040 : (x 15 4).toNat ≤ (x 15 12).toNat := himp _ _ (hp4 15)
    have b18041 := hb (x 15 4)
    have b18042 := hb (x 15 12)
    clear * - r18040 b18041 b18042 d18031
    omega
  have d18043 : (x 15 4 && x 15 8).toNat = 0 := by
    have r18044 := hand1 (x 15 4) (x 15 8)
    have b18045 := hb (x 15 4)
    have b18046 := hb (x 15 4 && x 15 8)
    clear * - r18044 b18045 b18046 d18039
    omega
  have d18047 : (x 13 2).toNat = 0 := by
    have r18048 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18049 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e18050 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b18051 := hb (x 12 3)
    have b18052 := hb (x 13 2)
    have b18053 := hb (x 14 13)
    have b18054 := hb (x 15 12)
    clear * - r18048 e18049 e18050 b18051 b18052 b18053 b18054 d18031 d18002
    omega
  have d18055 : (x 13 2 && x 13 6).toNat = 0 := by
    have r18056 := hand1 (x 13 2) (x 13 6)
    have b18057 := hb (x 13 2)
    have b18058 := hb (x 13 2 && x 13 6)
    clear * - r18056 b18057 b18058 d18047
    omega
  have d18059 : (x 13 10).toNat = 0 := by
    have r18060 : (x 13 10).toNat ≤ (x 13 2).toNat := himp _ _ (hp10 13)
    have b18061 := hb (x 13 2)
    have b18062 := hb (x 13 10)
    clear * - r18060 b18061 b18062 d18047
    omega
  have d18063 : (x 13 4 && x 13 10).toNat = 0 := by
    have r18064 := hand2 (x 13 4) (x 13 10)
    have b18065 := hb (x 13 10)
    have b18066 := hb (x 13 4 && x 13 10)
    clear * - r18064 b18065 b18066 d18059
    omega
  have d18067 : (x 13 6 && x 13 10).toNat = 0 := by
    have r18068 := hand2 (x 13 6) (x 13 10)
    have b18069 := hb (x 13 10)
    have b18070 := hb (x 13 6 && x 13 10)
    clear * - r18068 b18069 b18070 d18059
    omega
  have d18071 : (x 12 3).toNat = 0 := by
    have r18072 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18073 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e18074 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b18075 := hb (x 12 3)
    have b18076 := hb (x 13 2)
    have b18077 := hb (x 14 13)
    have b18078 := hb (x 15 12)
    clear * - r18072 e18073 e18074 b18075 b18076 b18077 b18078 d18031 d18002 d18047
    omega
  have d18079 : (x 12 3 && x 12 7).toNat = 0 := by
    have r18080 := hand1 (x 12 3) (x 12 7)
    have b18081 := hb (x 12 3)
    have b18082 := hb (x 12 3 && x 12 7)
    clear * - r18080 b18081 b18082 d18071
    omega
  have d18083 : (x 12 11).toNat = 0 := by
    have r18084 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
    have b18085 := hb (x 12 3)
    have b18086 := hb (x 12 11)
    clear * - r18084 b18085 b18086 d18071
    omega
  have d18087 : (x 12 5 && x 12 11).toNat = 0 := by
    have r18088 := hand2 (x 12 5) (x 12 11)
    have b18089 := hb (x 12 11)
    have b18090 := hb (x 12 5 && x 12 11)
    clear * - r18088 b18089 b18090 d18083
    omega
  have d18091 : (x 12 7 && x 12 11).toNat = 0 := by
    have r18092 := hand2 (x 12 7) (x 12 11)
    have b18093 := hb (x 12 11)
    have b18094 := hb (x 12 7 && x 12 11)
    clear * - r18092 b18093 b18094 d18083
    omega
  have d18095 : (x 11 3).toNat = 0 := by
    have r18096 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18097 := hb (x 0 14)
    have b18098 := hb (x 1 13)
    have b18099 := hb (x 2 12)
    have b18100 := hb (x 3 11)
    have b18101 := hb (x 4 10)
    have b18102 := hb (x 5 9)
    have b18103 := hb (x 6 8)
    have b18104 := hb (x 7 7)
    have b18105 := hb (x 8 6)
    have b18106 := hb (x 9 5)
    have b18107 := hb (x 10 4)
    have b18108 := hb (x 11 3)
    have b18109 := hb (x 12 2)
    have b18110 := hb (x 13 1)
    clear * - r18096 b18097 b18098 b18099 b18100 b18101 b18102 b18103 b18104 b18105 b18106 b18107 b18108 b18109 b18110 d17950 d17978 d17524 d17548 d17934 d17842 d17742 d17758 d17441 d17453 d17301 d17325 d17256
    omega
  have d18111 : (x 11 3 && x 11 14).toNat = 0 := by
    have r18112 := hand1 (x 11 3) (x 11 14)
    have b18113 := hb (x 11 3)
    have b18114 := hb (x 11 3 && x 11 14)
    clear * - r18112 b18113 b18114 d18095
    omega
  have d18115 : (x 14 11).toNat = 1 := by
    have r18116 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18117 := hb (x 10 4)
    have b18118 := hb (x 14 11)
    have b18119 := hb (x 13 1 && x 13 12)
    have b18120 := hb (x 12 2 && x 12 13)
    have b18121 := hb (x 11 3 && x 11 14)
    clear * - r18116 b18117 b18118 b18119 b18120 b18121 d17970 d17994 d18111 d17524
    omega
  have d18122 : (x 14 3).toNat = 1 := by
    have r18123 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
    have b18124 := hb (x 14 3)
    have b18125 := hb (x 14 11)
    clear * - r18123 b18124 b18125 d18115
    omega
  have d18126 : (x 17 12).toNat = 0 := by
    have r18127 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18128 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e18129 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b18130 := hb (x 14 3)
    have b18131 := hb (x 15 2)
    have b18132 := hb (x 16 13)
    have b18133 := hb (x 17 12)
    clear * - r18127 e18128 e18129 b18130 b18131 b18132 b18133 d18019 d18122
    omega
  have d18134 : (x 16 13).toNat = 0 := by
    have r18135 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18136 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e18137 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have b18138 := hb (x 14 3)
    have b18139 := hb (x 15 2)
    have b18140 := hb (x 16 13)
    have b18141 := hb (x 17 12)
    clear * - r18135 e18136 e18137 b18138 b18139 b18140 b18141 d18126 d18019 d18122
    omega
  have d18142 : (x 14 2).toNat = 1 := by
    have r18143 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18144 := hb (x 14 2)
    have b18145 := hb (x 16 13)
    have b18146 := hb (x 15 1 && x 15 14)
    clear * - r18143 b18144 b18145 b18146 d18134 d18015
    omega
  have d18147 : (x 16 12).toNat = 0 := by
    have r18148 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18149 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e18150 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b18151 := hb (x 13 3)
    have b18152 := hb (x 14 2)
    have b18153 := hb (x 15 13)
    have b18154 := hb (x 16 12)
    clear * - r18148 e18149 e18150 b18151 b18152 b18153 b18154 d18142
    omega
  have d18155 : (x 15 13).toNat = 0 := by
    have r18156 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18157 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e18158 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b18159 := hb (x 13 3)
    have b18160 := hb (x 14 2)
    have b18161 := hb (x 15 13)
    have b18162 := hb (x 16 12)
    clear * - r18156 e18157 e18158 b18159 b18160 b18161 b18162 d18147 d18142
    omega
  have d18163 : (x 13 3).toNat = 0 := by
    have r18164 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18165 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e18166 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b18167 := hb (x 13 3)
    have b18168 := hb (x 14 2)
    have b18169 := hb (x 15 13)
    have b18170 := hb (x 16 12)
    clear * - r18164 e18165 e18166 b18167 b18168 b18169 b18170 d18147 d18155 d18142
    omega
  have d18171 : (x 13 11).toNat = 0 := by
    have r18172 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
    have b18173 := hb (x 13 3)
    have b18174 := hb (x 13 11)
    clear * - r18172 b18173 b18174 d18163
    omega
  have d18175 : (x 17 8).toNat = 0 := by
    have r18176 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18177 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e18178 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e18179 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e18180 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e18181 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e18182 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b18183 := hb (x 10 7)
    have b18184 := hb (x 11 6)
    have b18185 := hb (x 12 5)
    have b18186 := hb (x 13 4)
    have b18187 := hb (x 14 11)
    have b18188 := hb (x 15 10)
    have b18189 := hb (x 16 9)
    have b18190 := hb (x 17 8)
    clear * - r18176 e18177 e18178 e18179 e18180 e18181 e18182 b18183 b18184 b18185 b18186 b18187 b18188 b18189 b18190 d18027 d18115
    omega
  have d18191 : (x 16 9).toNat = 0 := by
    have r18192 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18193 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e18194 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e18195 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e18196 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e18197 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e18198 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b18199 := hb (x 10 7)
    have b18200 := hb (x 11 6)
    have b18201 := hb (x 12 5)
    have b18202 := hb (x 13 4)
    have b18203 := hb (x 14 11)
    have b18204 := hb (x 15 10)
    have b18205 := hb (x 16 9)
    have b18206 := hb (x 17 8)
    clear * - r18192 e18193 e18194 e18195 e18196 e18197 e18198 b18199 b18200 b18201 b18202 b18203 b18204 b18205 b18206 d18175 d18027 d18115
    omega
  have d18207 : (x 13 4).toNat = 0 := by
    have r18208 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18209 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e18210 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e18211 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e18212 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e18213 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e18214 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b18215 := hb (x 10 7)
    have b18216 := hb (x 11 6)
    have b18217 := hb (x 12 5)
    have b18218 := hb (x 13 4)
    have b18219 := hb (x 14 11)
    have b18220 := hb (x 15 10)
    have b18221 := hb (x 16 9)
    have b18222 := hb (x 17 8)
    clear * - r18208 e18209 e18210 e18211 e18212 e18213 e18214 b18215 b18216 b18217 b18218 b18219 b18220 b18221 b18222 d18175 d18191 d18027 d18115
    omega
  have d18223 : (x 12 5).toNat = 0 := by
    have r18224 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18225 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e18226 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e18227 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e18228 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e18229 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e18230 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b18231 := hb (x 10 7)
    have b18232 := hb (x 11 6)
    have b18233 := hb (x 12 5)
    have b18234 := hb (x 13 4)
    have b18235 := hb (x 14 11)
    have b18236 := hb (x 15 10)
    have b18237 := hb (x 16 9)
    have b18238 := hb (x 17 8)
    clear * - r18224 e18225 e18226 e18227 e18228 e18229 e18230 b18231 b18232 b18233 b18234 b18235 b18236 b18237 b18238 d18175 d18191 d18027 d18115 d18207
    omega
  have d18239 : (x 11 6).toNat = 0 := by
    have r18240 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18241 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e18242 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e18243 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e18244 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e18245 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e18246 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b18247 := hb (x 10 7)
    have b18248 := hb (x 11 6)
    have b18249 := hb (x 12 5)
    have b18250 := hb (x 13 4)
    have b18251 := hb (x 14 11)
    have b18252 := hb (x 15 10)
    have b18253 := hb (x 16 9)
    have b18254 := hb (x 17 8)
    clear * - r18240 e18241 e18242 e18243 e18244 e18245 e18246 b18247 b18248 b18249 b18250 b18251 b18252 b18253 b18254 d18175 d18191 d18027 d18115 d18207 d18223
    omega
  have d18255 : (x 11 6 && x 11 12).toNat = 0 := by
    have r18256 := hand1 (x 11 6) (x 11 12)
    have b18257 := hb (x 11 6)
    have b18258 := hb (x 11 6 && x 11 12)
    clear * - r18256 b18257 b18258 d18239
    omega
  have d18259 : (x 10 7).toNat = 0 := by
    have r18260 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18261 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e18262 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e18263 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e18264 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e18265 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e18266 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have b18267 := hb (x 10 7)
    have b18268 := hb (x 11 6)
    have b18269 := hb (x 12 5)
    have b18270 := hb (x 13 4)
    have b18271 := hb (x 14 11)
    have b18272 := hb (x 15 10)
    have b18273 := hb (x 16 9)
    have b18274 := hb (x 17 8)
    clear * - r18260 e18261 e18262 e18263 e18264 e18265 e18266 b18267 b18268 b18269 b18270 b18271 b18272 b18273 b18274 d18175 d18191 d18027 d18115 d18207 d18223 d18239
    omega
  have d18275 : (x 10 7 && x 10 13).toNat = 0 := by
    have r18276 := hand1 (x 10 7) (x 10 13)
    have b18277 := hb (x 10 7)
    have b18278 := hb (x 10 7 && x 10 13)
    clear * - r18276 b18277 b18278 d18259
    omega
  have d18279 : (x 11 3 && x 11 13).toNat = 0 := by
    have r18280 := hand1 (x 11 3) (x 11 13)
    have b18281 := hb (x 11 3)
    have b18282 := hb (x 11 3 && x 11 13)
    clear * - r18280 b18281 b18282 d18095
    omega
  have d18283 : (x 14 10).toNat = 1 := by
    have r18284 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18285 := hb (x 9 5)
    have b18286 := hb (x 14 10)
    have b18287 := hb (x 13 1 && x 13 11)
    have b18288 := hb (x 12 2 && x 12 12)
    have b18289 := hb (x 11 3 && x 11 13)
    have b18290 := hb (x 10 4 && x 10 14)
    clear * - r18284 b18285 b18286 b18287 b18288 b18289 b18290 d17974 d17998 d18279 d17528 d17548
    omega
  have d18291 : (x 16 8).toNat = 0 := by
    have r18292 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18293 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e18294 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e18295 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e18296 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e18297 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e18298 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b18299 := hb (x 9 7)
    have b18300 := hb (x 10 6)
    have b18301 := hb (x 11 5)
    have b18302 := hb (x 12 4)
    have b18303 := hb (x 13 11)
    have b18304 := hb (x 14 10)
    have b18305 := hb (x 15 9)
    have b18306 := hb (x 16 8)
    clear * - r18292 e18293 e18294 e18295 e18296 e18297 e18298 b18299 b18300 b18301 b18302 b18303 b18304 b18305 b18306 d18283 d18171
    omega
  have d18307 : (x 15 9).toNat = 0 := by
    have r18308 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18309 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e18310 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e18311 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e18312 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e18313 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e18314 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b18315 := hb (x 9 7)
    have b18316 := hb (x 10 6)
    have b18317 := hb (x 11 5)
    have b18318 := hb (x 12 4)
    have b18319 := hb (x 13 11)
    have b18320 := hb (x 14 10)
    have b18321 := hb (x 15 9)
    have b18322 := hb (x 16 8)
    clear * - r18308 e18309 e18310 e18311 e18312 e18313 e18314 b18315 b18316 b18317 b18318 b18319 b18320 b18321 b18322 d18291 d18283 d18171
    omega
  have d18323 : (x 12 4).toNat = 0 := by
    have r18324 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18325 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e18326 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e18327 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e18328 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e18329 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e18330 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b18331 := hb (x 9 7)
    have b18332 := hb (x 10 6)
    have b18333 := hb (x 11 5)
    have b18334 := hb (x 12 4)
    have b18335 := hb (x 13 11)
    have b18336 := hb (x 14 10)
    have b18337 := hb (x 15 9)
    have b18338 := hb (x 16 8)
    clear * - r18324 e18325 e18326 e18327 e18328 e18329 e18330 b18331 b18332 b18333 b18334 b18335 b18336 b18337 b18338 d18291 d18307 d18283 d18171
    omega
  have d18339 : (x 11 5).toNat = 0 := by
    have r18340 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18341 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e18342 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e18343 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e18344 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e18345 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e18346 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b18347 := hb (x 9 7)
    have b18348 := hb (x 10 6)
    have b18349 := hb (x 11 5)
    have b18350 := hb (x 12 4)
    have b18351 := hb (x 13 11)
    have b18352 := hb (x 14 10)
    have b18353 := hb (x 15 9)
    have b18354 := hb (x 16 8)
    clear * - r18340 e18341 e18342 e18343 e18344 e18345 e18346 b18347 b18348 b18349 b18350 b18351 b18352 b18353 b18354 d18291 d18307 d18283 d18171 d18323
    omega
  have d18355 : (x 10 6).toNat = 0 := by
    have r18356 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18357 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e18358 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e18359 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e18360 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e18361 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e18362 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b18363 := hb (x 9 7)
    have b18364 := hb (x 10 6)
    have b18365 := hb (x 11 5)
    have b18366 := hb (x 12 4)
    have b18367 := hb (x 13 11)
    have b18368 := hb (x 14 10)
    have b18369 := hb (x 15 9)
    have b18370 := hb (x 16 8)
    clear * - r18356 e18357 e18358 e18359 e18360 e18361 e18362 b18363 b18364 b18365 b18366 b18367 b18368 b18369 b18370 d18291 d18307 d18283 d18171 d18323 d18339
    omega
  have d18371 : (x 9 7).toNat = 0 := by
    have r18372 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18373 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
    have e18374 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
    have e18375 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
    have e18376 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
    have e18377 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
    have e18378 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
    have b18379 := hb (x 9 7)
    have b18380 := hb (x 10 6)
    have b18381 := hb (x 11 5)
    have b18382 := hb (x 12 4)
    have b18383 := hb (x 13 11)
    have b18384 := hb (x 14 10)
    have b18385 := hb (x 15 9)
    have b18386 := hb (x 16 8)
    clear * - r18372 e18373 e18374 e18375 e18376 e18377 e18378 b18379 b18380 b18381 b18382 b18383 b18384 b18385 b18386 d18291 d18307 d18283 d18171 d18323 d18339 d18355
    omega
  have d18387 : (x 9 1 && x 9 7).toNat = 0 := by
    have r18388 := hand2 (x 9 1) (x 9 7)
    have b18389 := hb (x 9 7)
    have b18390 := hb (x 9 1 && x 9 7)
    clear * - r18388 b18389 b18390 d18371
    omega
  have d18391 : (x 7 3 && x 7 9).toNat = 1 := by
    have r18392 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := by have q := hcov6 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18393 := hb (x 1 9)
    have b18394 := hb (x 10 6)
    have b18395 := hb (x 9 1 && x 9 7)
    have b18396 := hb (x 8 2 && x 8 8)
    have b18397 := hb (x 7 3 && x 7 9)
    have b18398 := hb (x 6 4 && x 6 10)
    have b18399 := hb (x 5 5 && x 5 11)
    have b18400 := hb (x 4 6 && x 4 12)
    have b18401 := hb (x 3 7 && x 3 13)
    have b18402 := hb (x 2 8 && x 2 14)
    clear * - r18392 b18393 b18394 b18395 b18396 b18397 b18398 b18399 b18400 b18401 b18402 d18355 d18387 d17560 d17477 d17576 d17429 d17734 d17790 d17794
    omega
  have d18403 : (x 7 9).toNat = 1 := by
    have r18404 := hand2 (x 7 3) (x 7 9)
    have b18405 := hb (x 7 9)
    have b18406 := hb (x 7 3 && x 7 9)
    clear * - r18404 b18405 b18406 d18391
    omega
  have d18407 : (x 7 1).toNat = 1 := by
    have r18408 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
    have b18409 := hb (x 7 1)
    have b18410 := hb (x 7 9)
    clear * - r18408 b18409 b18410 d18403
    omega
  have d18411 : (x 8 14).toNat = 0 := by
    have r18412 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18413 := hb (x 7 1)
    have b18414 := hb (x 8 14)
    clear * - r18412 b18413 b18414 d18407
    omega
  have d18415 : (x 8 1 && x 8 14).toNat = 0 := by
    have r18416 := hand2 (x 8 1) (x 8 14)
    have b18417 := hb (x 8 14)
    have b18418 := hb (x 8 1 && x 8 14)
    clear * - r18416 b18417 b18418 d18411
    omega
  have d18419 : (x 7 2).toNat = 1 := by
    have r18420 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18421 := hb (x 7 2)
    have b18422 := hb (x 9 13)
    have b18423 := hb (x 8 1 && x 8 14)
    clear * - r18420 b18421 b18422 b18423 d17532 d18415
    omega
  have d18424 : (x 7 14).toNat = 1 := by
    have r18425 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b18426 := hb (x 7 2)
    have b18427 := hb (x 7 14)
    clear * - r18425 b18426 b18427 d18419
    omega
  have d18428 : (x 6 1).toNat = 0 := by
    have r18429 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18430 := hb (x 6 1)
    have b18431 := hb (x 7 14)
    clear * - r18429 b18430 b18431 d18424
    omega
  have d18432 : (x 6 1 && x 6 11).toNat = 0 := by
    have r18433 := hand1 (x 6 1) (x 6 11)
    have b18434 := hb (x 6 1)
    have b18435 := hb (x 6 1 && x 6 11)
    clear * - r18433 b18434 b18435 d18428
    omega
  have d18436 : (x 7 10).toNat = 1 := by
    have r18437 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18438 := hb (x 2 5)
    have b18439 := hb (x 7 10)
    have b18440 := hb (x 6 1 && x 6 11)
    have b18441 := hb (x 5 2 && x 5 12)
    have b18442 := hb (x 4 3 && x 4 13)
    have b18443 := hb (x 3 4 && x 3 14)
    clear * - r18437 b18438 b18439 b18440 b18441 b18442 b18443 d18432 d17662 d17678 g15 g4
    omega
  have d18444 : (x 9 8).toNat = 0 := by
    have r18445 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18446 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e18447 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e18448 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e18449 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e18450 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e18451 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b18452 := hb (x 2 7)
    have b18453 := hb (x 3 6)
    have b18454 := hb (x 4 5)
    have b18455 := hb (x 5 4)
    have b18456 := hb (x 6 11)
    have b18457 := hb (x 7 10)
    have b18458 := hb (x 8 9)
    have b18459 := hb (x 9 8)
    clear * - r18445 e18446 e18447 e18448 e18449 e18450 e18451 b18452 b18453 b18454 b18455 b18456 b18457 b18458 b18459 d18436 d17666 d17682
    omega
  have d18460 : (x 9 8 && x 9 14).toNat = 0 := by
    have r18461 := hand1 (x 9 8) (x 9 14)
    have b18462 := hb (x 9 8)
    have b18463 := hb (x 9 8 && x 9 14)
    clear * - r18461 b18462 b18463 d18444
    omega
  have d18464 : (x 8 9).toNat = 0 := by
    have r18465 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18466 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e18467 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e18468 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e18469 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e18470 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e18471 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b18472 := hb (x 2 7)
    have b18473 := hb (x 3 6)
    have b18474 := hb (x 4 5)
    have b18475 := hb (x 5 4)
    have b18476 := hb (x 6 11)
    have b18477 := hb (x 7 10)
    have b18478 := hb (x 8 9)
    have b18479 := hb (x 9 8)
    clear * - r18465 e18466 e18467 e18468 e18469 e18470 e18471 b18472 b18473 b18474 b18475 b18476 b18477 b18478 b18479 d18444 d18436 d17666 d17682
    omega
  have d18480 : (x 6 11).toNat = 0 := by
    have r18481 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18482 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e18483 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e18484 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e18485 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e18486 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e18487 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have b18488 := hb (x 2 7)
    have b18489 := hb (x 3 6)
    have b18490 := hb (x 4 5)
    have b18491 := hb (x 5 4)
    have b18492 := hb (x 6 11)
    have b18493 := hb (x 7 10)
    have b18494 := hb (x 8 9)
    have b18495 := hb (x 9 8)
    clear * - r18481 e18482 e18483 e18484 e18485 e18486 e18487 b18488 b18489 b18490 b18491 b18492 b18493 b18494 b18495 d18444 d18464 d18436 d17666 d17682
    omega
  have d18496 : (x 16 1).toNat = 0 := by
    have r18497 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18498 := hb (x 3 14)
    have b18499 := hb (x 4 13)
    have b18500 := hb (x 5 12)
    have b18501 := hb (x 6 11)
    have b18502 := hb (x 7 10)
    have b18503 := hb (x 8 9)
    have b18504 := hb (x 9 8)
    have b18505 := hb (x 10 7)
    have b18506 := hb (x 11 6)
    have b18507 := hb (x 12 5)
    have b18508 := hb (x 13 4)
    have b18509 := hb (x 14 3)
    have b18510 := hb (x 15 2)
    have b18511 := hb (x 16 1)
    clear * - r18497 b18498 b18499 b18500 b18501 b18502 b18503 b18504 b18505 b18506 b18507 b18508 b18509 b18510 b18511 d18019 d18122 d18207 d18223 d18239 d18259 d18444 d18464 d18436 d18480 d17654 d17670 d17589
    omega
  have d18512 : (x 16 1 && x 16 14).toNat = 0 := by
    have r18513 := hand1 (x 16 1) (x 16 14)
    have b18514 := hb (x 16 1)
    have b18515 := hb (x 16 1 && x 16 14)
    clear * - r18513 b18514 b18515 d18496
    omega
  have d18516 : (x 17 13).toNat = 1 := by
    have r18517 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18518 := hb (x 15 2)
    have b18519 := hb (x 17 13)
    have b18520 := hb (x 16 1 && x 16 14)
    clear * - r18517 b18518 b18519 b18520 d18512 d18019
    omega
  have d18521 : (x 18 12).toNat = 0 := by
    have r18522 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18523 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e18524 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b18525 := hb (x 15 3)
    have b18526 := hb (x 16 2)
    have b18527 := hb (x 17 13)
    have b18528 := hb (x 18 12)
    clear * - r18522 e18523 e18524 b18525 b18526 b18527 b18528 d18516
    omega
  have d18529 : (x 18 1 && x 18 12).toNat = 0 := by
    have r18530 := hand2 (x 18 1) (x 18 12)
    have b18531 := hb (x 18 12)
    have b18532 := hb (x 18 1 && x 18 12)
    clear * - r18530 b18531 b18532 d18521
    omega
  have d18533 : (x 18 4).toNat = 0 := by
    have r18534 : (x 18 4).toNat ≤ (x 18 12).toNat := himp _ _ (hp4 18)
    have b18535 := hb (x 18 4)
    have b18536 := hb (x 18 12)
    clear * - r18534 b18535 b18536 d18521
    omega
  have d18537 : (x 16 1 && x 16 7).toNat = 0 := by
    have r18538 := hand1 (x 16 1) (x 16 7)
    have b18539 := hb (x 16 1)
    have b18540 := hb (x 16 1 && x 16 7)
    clear * - r18538 b18539 b18540 d18496
    omega
  have d18541 : (x 6 13).toNat = 0 := by
    have r18542 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b18543 := hb (x 6 1)
    have b18544 := hb (x 6 13)
    clear * - r18542 b18543 b18544 d18428
    omega
  have d18545 : (x 6 5).toNat = 0 := by
    have r18546 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
    have b18547 := hb (x 6 5)
    have b18548 := hb (x 6 13)
    clear * - r18546 b18547 b18548 d18541
    omega
  have d18549 : (x 5 1 && x 5 14).toNat = 1 := by
    have r18550 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18551 := hb (x 4 2)
    have b18552 := hb (x 6 13)
    have b18553 := hb (x 5 1 && x 5 14)
    clear * - r18550 b18551 b18552 b18553 d18541 d17437
    omega
  have d18554 : (x 5 14).toNat = 1 := by
    have r18555 := hand2 (x 5 1) (x 5 14)
    have b18556 := hb (x 5 14)
    have b18557 := hb (x 5 1 && x 5 14)
    clear * - r18555 b18556 b18557 d18549
    omega
  have d18558 : (x 9 12).toNat = 0 := by
    have r18559 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18560 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e18561 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b18562 := hb (x 6 3)
    have b18563 := hb (x 7 2)
    have b18564 := hb (x 8 13)
    have b18565 := hb (x 9 12)
    clear * - r18559 e18560 e18561 b18562 b18563 b18564 b18565 d18419
    omega
  have d18566 : (x 9 2 && x 9 12).toNat = 0 := by
    have r18567 := hand2 (x 9 2) (x 9 12)
    have b18568 := hb (x 9 12)
    have b18569 := hb (x 9 2 && x 9 12)
    clear * - r18567 b18568 b18569 d18558
    omega
  have d18570 : (x 9 4).toNat = 0 := by
    have r18571 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
    have b18572 := hb (x 9 4)
    have b18573 := hb (x 9 12)
    clear * - r18571 b18572 b18573 d18558
    omega
  have d18574 : (x 8 13).toNat = 0 := by
    have r18575 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18576 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
    have e18577 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
    have b18578 := hb (x 6 3)
    have b18579 := hb (x 7 2)
    have b18580 := hb (x 8 13)
    have b18581 := hb (x 9 12)
    clear * - r18575 e18576 e18577 b18578 b18579 b18580 b18581 d18558 d18419
    omega
  have d18582 : (x 8 3 && x 8 13).toNat = 0 := by
    have r18583 := hand2 (x 8 3) (x 8 13)
    have b18584 := hb (x 8 13)
    have b18585 := hb (x 8 3 && x 8 13)
    clear * - r18583 b18584 b18585 d18574
    omega
  have d18586 : (x 8 5).toNat = 0 := by
    have r18587 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
    have b18588 := hb (x 8 5)
    have b18589 := hb (x 8 13)
    clear * - r18587 b18588 b18589 d18574
    omega
  have d18590 : (x 8 5 && x 8 14).toNat = 0 := by
    have r18591 := hand1 (x 8 5) (x 8 14)
    have b18592 := hb (x 8 5)
    have b18593 := hb (x 8 5 && x 8 14)
    clear * - r18591 b18592 b18593 d18586
    omega
  have d18594 : (x 7 6).toNat = 1 := by
    have r18595 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18596 := hb (x 7 6)
    have b18597 := hb (x 13 9)
    have b18598 := hb (x 12 1 && x 12 10)
    have b18599 := hb (x 11 2 && x 11 11)
    have b18600 := hb (x 10 3 && x 10 12)
    have b18601 := hb (x 9 4 && x 9 13)
    have b18602 := hb (x 8 5 && x 8 14)
    clear * - r18595 b18596 b18597 b18598 b18599 b18600 b18601 b18602 d17866 d17902 d17926 d17516 d17540 d18590
    omega
  have d18603 : (x 13 8).toNat = 0 := by
    have r18604 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18605 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e18606 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e18607 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e18608 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e18609 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e18610 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b18611 := hb (x 6 7)
    have b18612 := hb (x 7 6)
    have b18613 := hb (x 8 5)
    have b18614 := hb (x 9 4)
    have b18615 := hb (x 10 11)
    have b18616 := hb (x 11 10)
    have b18617 := hb (x 12 9)
    have b18618 := hb (x 13 8)
    clear * - r18604 e18605 e18606 e18607 e18608 e18609 e18610 b18611 b18612 b18613 b18614 b18615 b18616 b18617 b18618 d18570 d18586 d18594
    omega
  have d18619 : (x 12 9).toNat = 0 := by
    have r18620 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18621 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e18622 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e18623 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e18624 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e18625 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e18626 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b18627 := hb (x 6 7)
    have b18628 := hb (x 7 6)
    have b18629 := hb (x 8 5)
    have b18630 := hb (x 9 4)
    have b18631 := hb (x 10 11)
    have b18632 := hb (x 11 10)
    have b18633 := hb (x 12 9)
    have b18634 := hb (x 13 8)
    clear * - r18620 e18621 e18622 e18623 e18624 e18625 e18626 b18627 b18628 b18629 b18630 b18631 b18632 b18633 b18634 d18603 d18570 d18586 d18594
    omega
  have d18635 : (x 11 10).toNat = 0 := by
    have r18636 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18637 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e18638 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e18639 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e18640 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e18641 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e18642 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b18643 := hb (x 6 7)
    have b18644 := hb (x 7 6)
    have b18645 := hb (x 8 5)
    have b18646 := hb (x 9 4)
    have b18647 := hb (x 10 11)
    have b18648 := hb (x 11 10)
    have b18649 := hb (x 12 9)
    have b18650 := hb (x 13 8)
    clear * - r18636 e18637 e18638 e18639 e18640 e18641 e18642 b18643 b18644 b18645 b18646 b18647 b18648 b18649 b18650 d18603 d18619 d18570 d18586 d18594
    omega
  have d18651 : (x 10 11).toNat = 0 := by
    have r18652 : (x 13 8).toNat + (x 12 1 && x 12 9).toNat + (x 11 2 && x 11 10).toNat + (x 10 3 && x 10 11).toNat + (x 9 4 && x 9 12).toNat + (x 8 5 && x 8 13).toNat + (x 7 6 && x 7 14).toNat + (x 6 7).toNat = 1 := by have q := hd8 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18653 : (x 12 1 && x 12 9).toNat = (x 12 9).toNat := handr _ _ (fun h => hp9 12 (h))
    have e18654 : (x 11 2 && x 11 10).toNat = (x 11 10).toNat := handr _ _ (fun h => hp10 11 (h))
    have e18655 : (x 10 3 && x 10 11).toNat = (x 10 11).toNat := handr _ _ (fun h => hp11 10 (h))
    have e18656 : (x 9 4 && x 9 12).toNat = (x 9 4).toNat := handl _ _ (fun h => hp4 9 (h))
    have e18657 : (x 8 5 && x 8 13).toNat = (x 8 5).toNat := handl _ _ (fun h => hp5 8 (h))
    have e18658 : (x 7 6 && x 7 14).toNat = (x 7 6).toNat := handl _ _ (fun h => hp6 7 (h))
    have b18659 := hb (x 6 7)
    have b18660 := hb (x 7 6)
    have b18661 := hb (x 8 5)
    have b18662 := hb (x 9 4)
    have b18663 := hb (x 10 11)
    have b18664 := hb (x 11 10)
    have b18665 := hb (x 12 9)
    have b18666 := hb (x 13 8)
    clear * - r18652 e18653 e18654 e18655 e18656 e18657 e18658 b18659 b18660 b18661 b18662 b18663 b18664 b18665 b18666 d18603 d18619 d18635 d18570 d18586 d18594
    omega
  have d18667 : (x 10 1 && x 10 11).toNat = 0 := by
    have r18668 := hand2 (x 10 1) (x 10 11)
    have b18669 := hb (x 10 11)
    have b18670 := hb (x 10 1 && x 10 11)
    clear * - r18668 b18669 b18670 d18651
    omega
  have d18671 : (x 7 4 && x 7 14).toNat = 1 := by
    have r18672 : 1 ≤ (x 11 10).toNat + (x 10 1 && x 10 11).toNat + (x 9 2 && x 9 12).toNat + (x 8 3 && x 8 13).toNat + (x 7 4 && x 7 14).toNat + (x 6 5).toNat := by have q := hcov10 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18673 := hb (x 6 5)
    have b18674 := hb (x 11 10)
    have b18675 := hb (x 10 1 && x 10 11)
    have b18676 := hb (x 9 2 && x 9 12)
    have b18677 := hb (x 8 3 && x 8 13)
    have b18678 := hb (x 7 4 && x 7 14)
    clear * - r18672 b18673 b18674 b18675 b18676 b18677 b18678 d18635 d18667 d18566 d18582 d18545
    omega
  have d18679 : (x 7 4).toNat = 1 := by
    have r18680 := hand1 (x 7 4) (x 7 14)
    have b18681 := hb (x 7 4)
    have b18682 := hb (x 7 4 && x 7 14)
    clear * - r18680 b18681 b18682 d18671
    omega
  have d18683 : (x 7 12).toNat = 1 := by
    have r18684 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b18685 := hb (x 7 4)
    have b18686 := hb (x 7 12)
    clear * - r18684 b18685 b18686 d18679
    omega
  have d18687 : (x 11 8).toNat = 0 := by
    have r18688 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18689 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e18690 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e18691 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e18692 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e18693 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e18694 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b18695 := hb (x 4 7)
    have b18696 := hb (x 5 6)
    have b18697 := hb (x 6 5)
    have b18698 := hb (x 7 4)
    have b18699 := hb (x 8 11)
    have b18700 := hb (x 9 10)
    have b18701 := hb (x 10 9)
    have b18702 := hb (x 11 8)
    clear * - r18688 e18689 e18690 e18691 e18692 e18693 e18694 b18695 b18696 b18697 b18698 b18699 b18700 b18701 b18702 d18679 d18545
    omega
  have d18703 : (x 11 8 && x 11 12).toNat = 0 := by
    have r18704 := hand1 (x 11 8) (x 11 12)
    have b18705 := hb (x 11 8)
    have b18706 := hb (x 11 8 && x 11 12)
    clear * - r18704 b18705 b18706 d18687
    omega
  have d18707 : (x 11 4 && x 11 8).toNat = 0 := by
    have r18708 := hand2 (x 11 4) (x 11 8)
    have b18709 := hb (x 11 8)
    have b18710 := hb (x 11 4 && x 11 8)
    clear * - r18708 b18709 b18710 d18687
    omega
  have d18711 : (x 10 9).toNat = 0 := by
    have r18712 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18713 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e18714 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e18715 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e18716 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e18717 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e18718 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b18719 := hb (x 4 7)
    have b18720 := hb (x 5 6)
    have b18721 := hb (x 6 5)
    have b18722 := hb (x 7 4)
    have b18723 := hb (x 8 11)
    have b18724 := hb (x 9 10)
    have b18725 := hb (x 10 9)
    have b18726 := hb (x 11 8)
    clear * - r18712 e18713 e18714 e18715 e18716 e18717 e18718 b18719 b18720 b18721 b18722 b18723 b18724 b18725 b18726 d18687 d18679 d18545
    omega
  have d18727 : (x 10 9 && x 10 13).toNat = 0 := by
    have r18728 := hand1 (x 10 9) (x 10 13)
    have b18729 := hb (x 10 9)
    have b18730 := hb (x 10 9 && x 10 13)
    clear * - r18728 b18729 b18730 d18711
    omega
  have d18731 : (x 10 5 && x 10 9).toNat = 0 := by
    have r18732 := hand2 (x 10 5) (x 10 9)
    have b18733 := hb (x 10 9)
    have b18734 := hb (x 10 5 && x 10 9)
    clear * - r18732 b18733 b18734 d18711
    omega
  have d18735 : (x 9 10).toNat = 0 := by
    have r18736 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18737 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e18738 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e18739 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e18740 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e18741 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e18742 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b18743 := hb (x 4 7)
    have b18744 := hb (x 5 6)
    have b18745 := hb (x 6 5)
    have b18746 := hb (x 7 4)
    have b18747 := hb (x 8 11)
    have b18748 := hb (x 9 10)
    have b18749 := hb (x 10 9)
    have b18750 := hb (x 11 8)
    clear * - r18736 e18737 e18738 e18739 e18740 e18741 e18742 b18743 b18744 b18745 b18746 b18747 b18748 b18749 b18750 d18687 d18711 d18679 d18545
    omega
  have d18751 : (x 9 6 && x 9 10).toNat = 0 := by
    have r18752 := hand2 (x 9 6) (x 9 10)
    have b18753 := hb (x 9 10)
    have b18754 := hb (x 9 6 && x 9 10)
    clear * - r18752 b18753 b18754 d18735
    omega
  have d18755 : (x 8 11).toNat = 0 := by
    have r18756 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18757 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e18758 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e18759 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e18760 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e18761 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e18762 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have b18763 := hb (x 4 7)
    have b18764 := hb (x 5 6)
    have b18765 := hb (x 6 5)
    have b18766 := hb (x 7 4)
    have b18767 := hb (x 8 11)
    have b18768 := hb (x 9 10)
    have b18769 := hb (x 10 9)
    have b18770 := hb (x 11 8)
    clear * - r18756 e18757 e18758 e18759 e18760 e18761 e18762 b18763 b18764 b18765 b18766 b18767 b18768 b18769 b18770 d18687 d18711 d18735 d18679 d18545
    omega
  have d18771 : (x 8 7 && x 8 11).toNat = 0 := by
    have r18772 := hand2 (x 8 7) (x 8 11)
    have b18773 := hb (x 8 11)
    have b18774 := hb (x 8 7 && x 8 11)
    clear * - r18772 b18773 b18774 d18755
    omega
  have d18775 : (x 14 5).toNat = 1 := by
    have r18776 : 1 ≤ (x 15 4).toNat + (x 14 1 && x 14 5).toNat + (x 13 2 && x 13 6).toNat + (x 12 3 && x 12 7).toNat + (x 11 4 && x 11 8).toNat + (x 10 5 && x 10 9).toNat + (x 9 6 && x 9 10).toNat + (x 8 7 && x 8 11).toNat + (x 7 8 && x 7 12).toNat + (x 6 9 && x 6 13).toNat + (x 5 10 && x 5 14).toNat + (x 4 11).toNat := by have q := hcov4 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18777 : (x 14 1 && x 14 5).toNat = (x 14 5).toNat := handr _ _ (fun h => hp13 14 (hp5 14 (h)))
    have e18778 : (x 5 10 && x 5 14).toNat = (x 5 10).toNat := handl _ _ (fun h => hp2 5 (hp10 5 (h)))
    have b18779 := hb (x 4 11)
    have b18780 := hb (x 5 10)
    have b18781 := hb (x 14 5)
    have b18782 := hb (x 15 4)
    have b18783 := hb (x 13 2 && x 13 6)
    have b18784 := hb (x 12 3 && x 12 7)
    have b18785 := hb (x 11 4 && x 11 8)
    have b18786 := hb (x 10 5 && x 10 9)
    have b18787 := hb (x 9 6 && x 9 10)
    have b18788 := hb (x 8 7 && x 8 11)
    have b18789 := hb (x 7 8 && x 7 12)
    have b18790 := hb (x 6 9 && x 6 13)
    clear * - r18776 e18777 e18778 b18779 b18780 b18781 b18782 b18783 b18784 b18785 b18786 b18787 b18788 b18789 b18790 d18039 d18055 d18079 d18707 d18731 d18751 d18771 g10 g11 g7 g6
    omega
  have d18791 : (x 19 8).toNat = 0 := by
    have r18792 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18793 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e18794 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e18795 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e18796 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e18797 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e18798 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b18799 := hb (x 12 7)
    have b18800 := hb (x 13 6)
    have b18801 := hb (x 14 5)
    have b18802 := hb (x 15 4)
    have b18803 := hb (x 16 11)
    have b18804 := hb (x 17 10)
    have b18805 := hb (x 18 9)
    have b18806 := hb (x 19 8)
    clear * - r18792 e18793 e18794 e18795 e18796 e18797 e18798 b18799 b18800 b18801 b18802 b18803 b18804 b18805 b18806 d18039 d18775
    omega
  have d18807 : (x 18 9).toNat = 0 := by
    have r18808 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18809 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e18810 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e18811 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e18812 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e18813 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e18814 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b18815 := hb (x 12 7)
    have b18816 := hb (x 13 6)
    have b18817 := hb (x 14 5)
    have b18818 := hb (x 15 4)
    have b18819 := hb (x 16 11)
    have b18820 := hb (x 17 10)
    have b18821 := hb (x 18 9)
    have b18822 := hb (x 19 8)
    clear * - r18808 e18809 e18810 e18811 e18812 e18813 e18814 b18815 b18816 b18817 b18818 b18819 b18820 b18821 b18822 d18791 d18039 d18775
    omega
  have d18823 : (x 17 10).toNat = 0 := by
    have r18824 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18825 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e18826 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e18827 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e18828 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e18829 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e18830 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b18831 := hb (x 12 7)
    have b18832 := hb (x 13 6)
    have b18833 := hb (x 14 5)
    have b18834 := hb (x 15 4)
    have b18835 := hb (x 16 11)
    have b18836 := hb (x 17 10)
    have b18837 := hb (x 18 9)
    have b18838 := hb (x 19 8)
    clear * - r18824 e18825 e18826 e18827 e18828 e18829 e18830 b18831 b18832 b18833 b18834 b18835 b18836 b18837 b18838 d18791 d18807 d18039 d18775
    omega
  have d18839 : (x 16 11).toNat = 0 := by
    have r18840 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18841 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e18842 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e18843 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e18844 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e18845 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e18846 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b18847 := hb (x 12 7)
    have b18848 := hb (x 13 6)
    have b18849 := hb (x 14 5)
    have b18850 := hb (x 15 4)
    have b18851 := hb (x 16 11)
    have b18852 := hb (x 17 10)
    have b18853 := hb (x 18 9)
    have b18854 := hb (x 19 8)
    clear * - r18840 e18841 e18842 e18843 e18844 e18845 e18846 b18847 b18848 b18849 b18850 b18851 b18852 b18853 b18854 d18791 d18807 d18823 d18039 d18775
    omega
  have d18855 : (x 13 6).toNat = 0 := by
    have r18856 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18857 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e18858 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e18859 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e18860 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e18861 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e18862 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b18863 := hb (x 12 7)
    have b18864 := hb (x 13 6)
    have b18865 := hb (x 14 5)
    have b18866 := hb (x 15 4)
    have b18867 := hb (x 16 11)
    have b18868 := hb (x 17 10)
    have b18869 := hb (x 18 9)
    have b18870 := hb (x 19 8)
    clear * - r18856 e18857 e18858 e18859 e18860 e18861 e18862 b18863 b18864 b18865 b18866 b18867 b18868 b18869 b18870 d18791 d18807 d18823 d18839 d18039 d18775
    omega
  have d18871 : (x 12 7).toNat = 0 := by
    have r18872 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18873 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e18874 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e18875 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e18876 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e18877 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e18878 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have b18879 := hb (x 12 7)
    have b18880 := hb (x 13 6)
    have b18881 := hb (x 14 5)
    have b18882 := hb (x 15 4)
    have b18883 := hb (x 16 11)
    have b18884 := hb (x 17 10)
    have b18885 := hb (x 18 9)
    have b18886 := hb (x 19 8)
    clear * - r18872 e18873 e18874 e18875 e18876 e18877 e18878 b18879 b18880 b18881 b18882 b18883 b18884 b18885 b18886 d18791 d18807 d18823 d18839 d18039 d18775 d18855
    omega
  have d18887 : (x 18 1).toNat = 0 := by
    have r18888 : (x 18 1).toNat + (x 17 2).toNat + (x 16 3).toNat + (x 15 4).toNat + (x 14 5).toNat + (x 13 6).toNat + (x 12 7).toNat + (x 11 8).toNat + (x 10 9).toNat + (x 9 10).toNat + (x 8 11).toNat + (x 7 12).toNat + (x 6 13).toNat + (x 5 14).toNat = 3 := by have q := hcount 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18889 := hb (x 5 14)
    have b18890 := hb (x 6 13)
    have b18891 := hb (x 7 12)
    have b18892 := hb (x 8 11)
    have b18893 := hb (x 9 10)
    have b18894 := hb (x 10 9)
    have b18895 := hb (x 11 8)
    have b18896 := hb (x 12 7)
    have b18897 := hb (x 13 6)
    have b18898 := hb (x 14 5)
    have b18899 := hb (x 15 4)
    have b18900 := hb (x 16 3)
    have b18901 := hb (x 17 2)
    have b18902 := hb (x 18 1)
    clear * - r18888 b18889 b18890 b18891 b18892 b18893 b18894 b18895 b18896 b18897 b18898 b18899 b18900 b18901 b18902 d18039 d18775 d18855 d18871 d18687 d18711 d18735 d18755 d18683 d18541 d18554
    omega
  have d18903 : (x 18 13).toNat = 0 := by
    have r18904 : (x 18 13).toNat ≤ (x 18 1).toNat := himp _ _ (hp13 18)
    have b18905 := hb (x 18 1)
    have b18906 := hb (x 18 13)
    clear * - r18904 b18905 b18906 d18887
    omega
  have d18907 : (x 18 5).toNat = 0 := by
    have r18908 : (x 18 5).toNat ≤ (x 18 13).toNat := himp _ _ (hp5 18)
    have b18909 := hb (x 18 5)
    have b18910 := hb (x 18 13)
    clear * - r18908 b18909 b18910 d18903
    omega
  have d18911 : (x 17 2).toNat = 0 := by
    have r18912 : (x 18 1).toNat + (x 17 2).toNat + (x 16 3).toNat + (x 15 4).toNat + (x 14 5).toNat + (x 13 6).toNat + (x 12 7).toNat + (x 11 8).toNat + (x 10 9).toNat + (x 9 10).toNat + (x 8 11).toNat + (x 7 12).toNat + (x 6 13).toNat + (x 5 14).toNat = 3 := by have q := hcount 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18913 := hb (x 5 14)
    have b18914 := hb (x 6 13)
    have b18915 := hb (x 7 12)
    have b18916 := hb (x 8 11)
    have b18917 := hb (x 9 10)
    have b18918 := hb (x 10 9)
    have b18919 := hb (x 11 8)
    have b18920 := hb (x 12 7)
    have b18921 := hb (x 13 6)
    have b18922 := hb (x 14 5)
    have b18923 := hb (x 15 4)
    have b18924 := hb (x 16 3)
    have b18925 := hb (x 17 2)
    have b18926 := hb (x 18 1)
    clear * - r18912 b18913 b18914 b18915 b18916 b18917 b18918 b18919 b18920 b18921 b18922 b18923 b18924 b18925 b18926 d18887 d18039 d18775 d18855 d18871 d18687 d18711 d18735 d18755 d18683 d18541 d18554
    omega
  have d18927 : (x 17 2 && x 17 13).toNat = 0 := by
    have r18928 := hand1 (x 17 2) (x 17 13)
    have b18929 := hb (x 17 2)
    have b18930 := hb (x 17 2 && x 17 13)
    clear * - r18928 b18929 b18930 d18911
    omega
  have d18931 : (x 17 2 && x 17 6).toNat = 0 := by
    have r18932 := hand1 (x 17 2) (x 17 6)
    have b18933 := hb (x 17 2)
    have b18934 := hb (x 17 2 && x 17 6)
    clear * - r18932 b18933 b18934 d18911
    omega
  have d18935 : (x 16 3).toNat = 0 := by
    have r18936 : (x 18 1).toNat + (x 17 2).toNat + (x 16 3).toNat + (x 15 4).toNat + (x 14 5).toNat + (x 13 6).toNat + (x 12 7).toNat + (x 11 8).toNat + (x 10 9).toNat + (x 9 10).toNat + (x 8 11).toNat + (x 7 12).toNat + (x 6 13).toNat + (x 5 14).toNat = 3 := by have q := hcount 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18937 := hb (x 5 14)
    have b18938 := hb (x 6 13)
    have b18939 := hb (x 7 12)
    have b18940 := hb (x 8 11)
    have b18941 := hb (x 9 10)
    have b18942 := hb (x 10 9)
    have b18943 := hb (x 11 8)
    have b18944 := hb (x 12 7)
    have b18945 := hb (x 13 6)
    have b18946 := hb (x 14 5)
    have b18947 := hb (x 15 4)
    have b18948 := hb (x 16 3)
    have b18949 := hb (x 17 2)
    have b18950 := hb (x 18 1)
    clear * - r18936 b18937 b18938 b18939 b18940 b18941 b18942 b18943 b18944 b18945 b18946 b18947 b18948 b18949 b18950 d18887 d18911 d18039 d18775 d18855 d18871 d18687 d18711 d18735 d18755 d18683 d18541 d18554
    omega
  have d18951 : (x 16 3 && x 16 14).toNat = 0 := by
    have r18952 := hand1 (x 16 3) (x 16 14)
    have b18953 := hb (x 16 3)
    have b18954 := hb (x 16 3 && x 16 14)
    clear * - r18952 b18953 b18954 d18935
    omega
  have d18955 : (x 19 11).toNat = 1 := by
    have r18956 : 1 ≤ (x 19 11).toNat + (x 18 1 && x 18 12).toNat + (x 17 2 && x 17 13).toNat + (x 16 3 && x 16 14).toNat + (x 15 4).toNat := by have q := hcov11 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18957 := hb (x 15 4)
    have b18958 := hb (x 19 11)
    have b18959 := hb (x 18 1 && x 18 12)
    have b18960 := hb (x 17 2 && x 17 13)
    have b18961 := hb (x 16 3 && x 16 14)
    clear * - r18956 b18957 b18958 b18959 b18960 b18961 d18529 d18927 d18951 d18039
    omega
  have d18962 : (x 22 8).toNat = 0 := by
    have r18963 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18964 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
    have e18965 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
    have e18966 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
    have e18967 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
    have e18968 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
    have e18969 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
    have b18970 := hb (x 15 7)
    have b18971 := hb (x 16 6)
    have b18972 := hb (x 17 5)
    have b18973 := hb (x 18 4)
    have b18974 := hb (x 19 11)
    have b18975 := hb (x 20 10)
    have b18976 := hb (x 21 9)
    have b18977 := hb (x 22 8)
    clear * - r18963 e18964 e18965 e18966 e18967 e18968 e18969 b18970 b18971 b18972 b18973 b18974 b18975 b18976 b18977 d18955 d18533
    omega
  have d18978 : (x 21 9).toNat = 0 := by
    have r18979 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18980 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
    have e18981 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
    have e18982 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
    have e18983 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
    have e18984 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
    have e18985 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
    have b18986 := hb (x 15 7)
    have b18987 := hb (x 16 6)
    have b18988 := hb (x 17 5)
    have b18989 := hb (x 18 4)
    have b18990 := hb (x 19 11)
    have b18991 := hb (x 20 10)
    have b18992 := hb (x 21 9)
    have b18993 := hb (x 22 8)
    clear * - r18979 e18980 e18981 e18982 e18983 e18984 e18985 b18986 b18987 b18988 b18989 b18990 b18991 b18992 b18993 d18962 d18955 d18533
    omega
  have d18994 : (x 20 10).toNat = 0 := by
    have r18995 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18996 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
    have e18997 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
    have e18998 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
    have e18999 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
    have e19000 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
    have e19001 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
    have b19002 := hb (x 15 7)
    have b19003 := hb (x 16 6)
    have b19004 := hb (x 17 5)
    have b19005 := hb (x 18 4)
    have b19006 := hb (x 19 11)
    have b19007 := hb (x 20 10)
    have b19008 := hb (x 21 9)
    have b19009 := hb (x 22 8)
    clear * - r18995 e18996 e18997 e18998 e18999 e19000 e19001 b19002 b19003 b19004 b19005 b19006 b19007 b19008 b19009 d18962 d18978 d18955 d18533
    omega
  have d19010 : (x 17 5).toNat = 0 := by
    have r19011 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19012 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
    have e19013 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
    have e19014 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
    have e19015 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
    have e19016 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
    have e19017 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
    have b19018 := hb (x 15 7)
    have b19019 := hb (x 16 6)
    have b19020 := hb (x 17 5)
    have b19021 := hb (x 18 4)
    have b19022 := hb (x 19 11)
    have b19023 := hb (x 20 10)
    have b19024 := hb (x 21 9)
    have b19025 := hb (x 22 8)
    clear * - r19011 e19012 e19013 e19014 e19015 e19016 e19017 b19018 b19019 b19020 b19021 b19022 b19023 b19024 b19025 d18962 d18978 d18994 d18955 d18533
    omega
  have d19026 : (x 16 6).toNat = 0 := by
    have r19027 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19028 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
    have e19029 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
    have e19030 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
    have e19031 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
    have e19032 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
    have e19033 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
    have b19034 := hb (x 15 7)
    have b19035 := hb (x 16 6)
    have b19036 := hb (x 17 5)
    have b19037 := hb (x 18 4)
    have b19038 := hb (x 19 11)
    have b19039 := hb (x 20 10)
    have b19040 := hb (x 21 9)
    have b19041 := hb (x 22 8)
    clear * - r19027 e19028 e19029 e19030 e19031 e19032 e19033 b19034 b19035 b19036 b19037 b19038 b19039 b19040 b19041 d18962 d18978 d18994 d18955 d18533 d19010
    omega
  have d19042 : (x 15 7).toNat = 0 := by
    have r19043 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19044 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
    have e19045 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
    have e19046 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
    have e19047 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
    have e19048 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
    have e19049 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
    have b19050 := hb (x 15 7)
    have b19051 := hb (x 16 6)
    have b19052 := hb (x 17 5)
    have b19053 := hb (x 18 4)
    have b19054 := hb (x 19 11)
    have b19055 := hb (x 20 10)
    have b19056 := hb (x 21 9)
    have b19057 := hb (x 22 8)
    clear * - r19043 e19044 e19045 e19046 e19047 e19048 e19049 b19050 b19051 b19052 b19053 b19054 b19055 b19056 b19057 d18962 d18978 d18994 d18955 d18533 d19010 d19026
    omega
  have d19058 : (x 8 7 && x 8 14).toNat = 1 := by
    have r19059 : 1 ≤ (x 15 7).toNat + (x 14 1 && x 14 8).toNat + (x 13 2 && x 13 9).toNat + (x 12 3 && x 12 10).toNat + (x 11 4 && x 11 11).toNat + (x 10 5 && x 10 12).toNat + (x 9 6 && x 9 13).toNat + (x 8 7 && x 8 14).toNat + (x 7 8).toNat := by have q := hcov7 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b19060 := hb (x 7 8)
    have b19061 := hb (x 15 7)
    have b19062 := hb (x 14 1 && x 14 8)
    have b19063 := hb (x 13 2 && x 13 9)
    have b19064 := hb (x 12 3 && x 12 10)
    have b19065 := hb (x 11 4 && x 11 11)
    have b19066 := hb (x 10 5 && x 10 12)
    have b19067 := hb (x 9 6 && x 9 13)
    have b19068 := hb (x 8 7 && x 8 14)
    clear * - r19059 b19060 b19061 b19062 b19063 b19064 b19065 b19066 b19067 b19068 d19042 d17862 d17882 d17906 d17930 d17520 d17544 g9
    omega
  have d19069 : (x 8 7).toNat = 1 := by
    have r19070 := hand1 (x 8 7) (x 8 14)
    have b19071 := hb (x 8 7)
    have b19072 := hb (x 8 7 && x 8 14)
    clear * - r19070 b19071 b19072 d19058
    omega
  have d19073 : (x 15 8).toNat = 0 := by
    have r19074 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19075 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e19076 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e19077 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e19078 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e19079 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e19080 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b19081 := hb (x 8 7)
    have b19082 := hb (x 9 6)
    have b19083 := hb (x 10 5)
    have b19084 := hb (x 11 4)
    have b19085 := hb (x 12 11)
    have b19086 := hb (x 13 10)
    have b19087 := hb (x 14 9)
    have b19088 := hb (x 15 8)
    clear * - r19074 e19075 e19076 e19077 e19078 e19079 e19080 b19081 b19082 b19083 b19084 b19085 b19086 b19087 b19088 d18059 d18083 d19069
    omega
  have d19089 : (x 14 9).toNat = 0 := by
    have r19090 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19091 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
    have e19092 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
    have e19093 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
    have e19094 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
    have e19095 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
    have e19096 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
    have b19097 := hb (x 8 7)
    have b19098 := hb (x 9 6)
    have b19099 := hb (x 10 5)
    have b19100 := hb (x 11 4)
    have b19101 := hb (x 12 11)
    have b19102 := hb (x 13 10)
    have b19103 := hb (x 14 9)
    have b19104 := hb (x 15 8)
    clear * - r19090 e19091 e19092 e19093 e19094 e19095 e19096 b19097 b19098 b19099 b19100 b19101 b19102 b19103 b19104 d19073 d18059 d18083 d19069
    omega
  have d19105 : (x 14 3 && x 14 9).toNat = 0 := by
    have r19106 := hand2 (x 14 3) (x 14 9)
    have b19107 := hb (x 14 9)
    have b19108 := hb (x 14 3 && x 14 9)
    clear * - r19106 b19107 b19108 d19089
    omega
  have d19109 : (x 17 6).toNat = 1 := by
    have r19110 : 1 ≤ (x 17 6).toNat + (x 16 1 && x 16 7).toNat + (x 15 2 && x 15 8).toNat + (x 14 3 && x 14 9).toNat + (x 13 4 && x 13 10).toNat + (x 12 5 && x 12 11).toNat + (x 11 6 && x 11 12).toNat + (x 10 7 && x 10 13).toNat + (x 9 8 && x 9 14).toNat + (x 8 9).toNat := by have q := hcov6 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b19111 := hb (x 8 9)
    have b19112 := hb (x 17 6)
    have b19113 := hb (x 16 1 && x 16 7)
    have b19114 := hb (x 15 2 && x 15 8)
    have b19115 := hb (x 14 3 && x 14 9)
    have b19116 := hb (x 13 4 && x 13 10)
    have b19117 := hb (x 12 5 && x 12 11)
    have b19118 := hb (x 11 6 && x 11 12)
    have b19119 := hb (x 10 7 && x 10 13)
    have b19120 := hb (x 9 8 && x 9 14)
    clear * - r19110 b19111 b19112 b19113 b19114 b19115 b19116 b19117 b19118 b19119 b19120 d18537 d18023 d19105 d18063 d18087 d18255 d18275 d18460 d18464
    omega
  have d19121 : (x 23 8).toNat = 0 := by
    have r19122 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19123 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e19124 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e19125 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e19126 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e19127 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e19128 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b19129 := hb (x 16 7)
    have b19130 := hb (x 17 6)
    have b19131 := hb (x 18 5)
    have b19132 := hb (x 19 4)
    have b19133 := hb (x 20 11)
    have b19134 := hb (x 21 10)
    have b19135 := hb (x 22 9)
    have b19136 := hb (x 23 8)
    clear * - r19122 e19123 e19124 e19125 e19126 e19127 e19128 b19129 b19130 b19131 b19132 b19133 b19134 b19135 b19136 d18907 d19109
    omega
  have d19137 : (x 22 9).toNat = 0 := by
    have r19138 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19139 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e19140 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e19141 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e19142 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e19143 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e19144 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b19145 := hb (x 16 7)
    have b19146 := hb (x 17 6)
    have b19147 := hb (x 18 5)
    have b19148 := hb (x 19 4)
    have b19149 := hb (x 20 11)
    have b19150 := hb (x 21 10)
    have b19151 := hb (x 22 9)
    have b19152 := hb (x 23 8)
    clear * - r19138 e19139 e19140 e19141 e19142 e19143 e19144 b19145 b19146 b19147 b19148 b19149 b19150 b19151 b19152 d19121 d18907 d19109
    omega
  have d19153 : (x 21 10).toNat = 0 := by
    have r19154 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19155 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e19156 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e19157 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e19158 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e19159 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e19160 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b19161 := hb (x 16 7)
    have b19162 := hb (x 17 6)
    have b19163 := hb (x 18 5)
    have b19164 := hb (x 19 4)
    have b19165 := hb (x 20 11)
    have b19166 := hb (x 21 10)
    have b19167 := hb (x 22 9)
    have b19168 := hb (x 23 8)
    clear * - r19154 e19155 e19156 e19157 e19158 e19159 e19160 b19161 b19162 b19163 b19164 b19165 b19166 b19167 b19168 d19121 d19137 d18907 d19109
    omega
  have d19169 : (x 20 11).toNat = 0 := by
    have r19170 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19171 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e19172 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e19173 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e19174 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e19175 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e19176 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b19177 := hb (x 16 7)
    have b19178 := hb (x 17 6)
    have b19179 := hb (x 18 5)
    have b19180 := hb (x 19 4)
    have b19181 := hb (x 20 11)
    have b19182 := hb (x 21 10)
    have b19183 := hb (x 22 9)
    have b19184 := hb (x 23 8)
    clear * - r19170 e19171 e19172 e19173 e19174 e19175 e19176 b19177 b19178 b19179 b19180 b19181 b19182 b19183 b19184 d19121 d19137 d19153 d18907 d19109
    omega
  have d19185 : (x 19 4).toNat = 0 := by
    have r19186 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19187 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e19188 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e19189 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e19190 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e19191 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e19192 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b19193 := hb (x 16 7)
    have b19194 := hb (x 17 6)
    have b19195 := hb (x 18 5)
    have b19196 := hb (x 19 4)
    have b19197 := hb (x 20 11)
    have b19198 := hb (x 21 10)
    have b19199 := hb (x 22 9)
    have b19200 := hb (x 23 8)
    clear * - r19186 e19187 e19188 e19189 e19190 e19191 e19192 b19193 b19194 b19195 b19196 b19197 b19198 b19199 b19200 d19121 d19137 d19153 d19169 d18907 d19109
    omega
  have d19201 : (x 16 7).toNat = 0 := by
    have r19202 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19203 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
    have e19204 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
    have e19205 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
    have e19206 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
    have e19207 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
    have e19208 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
    have b19209 := hb (x 16 7)
    have b19210 := hb (x 17 6)
    have b19211 := hb (x 18 5)
    have b19212 := hb (x 19 4)
    have b19213 := hb (x 20 11)
    have b19214 := hb (x 21 10)
    have b19215 := hb (x 22 9)
    have b19216 := hb (x 23 8)
    clear * - r19202 e19203 e19204 e19205 e19206 e19207 e19208 b19209 b19210 b19211 b19212 b19213 b19214 b19215 b19216 d19121 d19137 d19153 d19169 d19185 d18907 d19109
    omega
  have d19217 : (x 16 3 && x 16 7).toNat = 0 := by
    have r19218 := hand2 (x 16 3) (x 16 7)
    have b19219 := hb (x 16 7)
    have b19220 := hb (x 16 3 && x 16 7)
    clear * - r19218 b19219 b19220 d19201
    omega
  have d19221 : (x 14 5 && x 14 9).toNat = 1 := by
    have r19222 : 1 ≤ (x 19 4).toNat + (x 18 1 && x 18 5).toNat + (x 17 2 && x 17 6).toNat + (x 16 3 && x 16 7).toNat + (x 15 4 && x 15 8).toNat + (x 14 5 && x 14 9).toNat + (x 13 6 && x 13 10).toNat + (x 12 7 && x 12 11).toNat + (x 11 8 && x 11 12).toNat + (x 10 9 && x 10 13).toNat + (x 9 10 && x 9 14).toNat + (x 8 11).toNat := by have q := hcov4 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19223 : (x 18 1 && x 18 5).toNat = (x 18 5).toNat := handr _ _ (fun h => hp13 18 (hp5 18 (h)))
    have e19224 : (x 9 10 && x 9 14).toNat = (x 9 10).toNat := handl _ _ (fun h => hp2 9 (hp10 9 (h)))
    have b19225 := hb (x 8 11)
    have b19226 := hb (x 9 10)
    have b19227 := hb (x 18 5)
    have b19228 := hb (x 19 4)
    have b19229 := hb (x 17 2 && x 17 6)
    have b19230 := hb (x 16 3 && x 16 7)
    have b19231 := hb (x 15 4 && x 15 8)
    have b19232 := hb (x 14 5 && x 14 9)
    have b19233 := hb (x 13 6 && x 13 10)
    have b19234 := hb (x 12 7 && x 12 11)
    have b19235 := hb (x 11 8 && x 11 12)
    have b19236 := hb (x 10 9 && x 10 13)
    clear * - r19222 e19223 e19224 b19225 b19226 b19227 b19228 b19229 b19230 b19231 b19232 b19233 b19234 b19235 b19236 d19185 d18907 d18931 d19217 d18043 d18067 d18091 d18703 d18727 d18735 d18755
    omega
  have r19237 := hand2 (x 14 5) (x 14 9)
  have b19238 := hb (x 14 9)
  have b19239 := hb (x 14 5 && x 14 9)
  linarith only [r19237, b19238, b19239, d19221, d19089]

theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b1001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 2).toNat = 1)
    (g1 : (x 0 6).toNat = 0)
    (g2 : (x 0 13).toNat = 0)
    (g3 : (x 1 2).toNat = 0)
    (g4 : (x 2 5).toNat = 0)
    (g5 : (x 3 4).toNat = 0)
    (g6 : (x 4 11).toNat = 0)
    (g7 : (x 5 10).toNat = 0)
    (g8 : (x 6 9).toNat = 0)
    (g9 : (x 7 8).toNat = 0)
    (g10 : (x 7 8 && x 7 12).toNat = 0)
    (g11 : (x 6 9 && x 6 13).toNat = 0)
    (g12 : (x 5 1 && x 5 10).toNat = 0)
    (g13 : (x 4 2 && x 4 11).toNat = 0)
    (g14 : (x 1 5 && x 1 14).toNat = 0)
    (g15 : (x 3 4 && x 3 14).toNat = 0)
    (g16 : (x 1 3 && x 1 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b1001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16
