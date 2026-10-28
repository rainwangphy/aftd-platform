import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b101

Topic: combinatorics   Node: d697202533bf

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_six_iff_seven_core: under the layer-free tight-cover constraints for k = 15 and 31 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b101_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 5).toNat = 0)
    (g1 : (x 0 6).toNat = 0)
    (g2 : (x 0 8).toNat = 1)
    (g3 : (x 0 13).toNat = 0)
    (g4 : (x 1 2).toNat = 0)
    (g5 : (x 1 6).toNat = 0)
    (g6 : (x 1 10).toNat = 0)
    (g7 : (x 2 5).toNat = 0)
    (g8 : (x 3 4).toNat = 0)
    (g9 : (x 4 11).toNat = 0)
    (g10 : (x 5 10).toNat = 0)
    (g11 : (x 6 9).toNat = 0)
    (g12 : (x 0 5 && x 0 9).toNat = 0)
    (g13 : (x 0 6 && x 0 10).toNat = 0)
    (g14 : (x 1 2 && x 1 7).toNat = 0)
    (g15 : (x 3 4 && x 3 11).toNat = 0)
    (g16 : (x 2 5 && x 2 12).toNat = 0)
    (g17 : (x 1 6 && x 1 13).toNat = 0)
    (g18 : (x 1 2 && x 1 11).toNat = 0)
    (g19 : (x 5 1 && x 5 10).toNat = 0)
    (g20 : (x 4 2 && x 4 11).toNat = 0)
    (g21 : (x 1 5 && x 1 14).toNat = 0)
    (g22 : (x 3 4 && x 3 13).toNat = 0)
    (g23 : (x 2 5 && x 2 14).toNat = 0)
    (g24 : (x 1 2 && x 1 12).toNat = 0)
    (g25 : (x 0 3 && x 0 13).toNat = 0)
    (g26 : (x 4 1 && x 4 11).toNat = 0)
    (g27 : (x 1 4 && x 1 14).toNat = 0)
    (g28 : (x 3 4 && x 3 14).toNat = 0)
    (g29 : (x 1 3 && x 1 14).toNat = 0)
    (g30 : (x 1 1 && x 1 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d19241 : (x (-1) 9).toNat = 0 := by
    have r19242 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19243 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e19244 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e19245 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e19246 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e19247 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e19248 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b19249 := hb (x (-7) 7)
    have b19250 := hb (x (-6) 6)
    have b19251 := hb (x (-5) 5)
    have b19252 := hb (x (-4) 4)
    have b19253 := hb (x (-3) 11)
    have b19254 := hb (x (-2) 10)
    have b19255 := hb (x (-1) 9)
    have b19256 := hb (x 0 8)
    clear * - r19242 e19243 e19244 e19245 e19246 e19247 e19248 b19249 b19250 b19251 b19252 b19253 b19254 b19255 b19256 g2
    omega
  have d19257 : (x (-1) 4 && x (-1) 9).toNat = 0 := by
    have r19258 := hand2 (x (-1) 4) (x (-1) 9)
    have b19259 := hb (x (-1) 9)
    have b19260 := hb (x (-1) 4 && x (-1) 9)
    clear * - r19258 b19259 b19260 d19241
    omega
  have d19261 : (x (-2) 10).toNat = 0 := by
    have r19262 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19263 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e19264 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e19265 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e19266 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e19267 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e19268 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b19269 := hb (x (-7) 7)
    have b19270 := hb (x (-6) 6)
    have b19271 := hb (x (-5) 5)
    have b19272 := hb (x (-4) 4)
    have b19273 := hb (x (-3) 11)
    have b19274 := hb (x (-2) 10)
    have b19275 := hb (x (-1) 9)
    have b19276 := hb (x 0 8)
    clear * - r19262 e19263 e19264 e19265 e19266 e19267 e19268 b19269 b19270 b19271 b19272 b19273 b19274 b19275 b19276 g2 d19241
    omega
  have d19277 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
    have r19278 := hand2 (x (-2) 1) (x (-2) 10)
    have b19279 := hb (x (-2) 10)
    have b19280 := hb (x (-2) 1 && x (-2) 10)
    clear * - r19278 b19279 b19280 d19261
    omega
  have d19281 : (x (-2) 5 && x (-2) 10).toNat = 0 := by
    have r19282 := hand2 (x (-2) 5) (x (-2) 10)
    have b19283 := hb (x (-2) 10)
    have b19284 := hb (x (-2) 5 && x (-2) 10)
    clear * - r19282 b19283 b19284 d19261
    omega
  have d19285 : (x (-3) 11).toNat = 0 := by
    have r19286 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19287 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e19288 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e19289 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e19290 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e19291 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e19292 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b19293 := hb (x (-7) 7)
    have b19294 := hb (x (-6) 6)
    have b19295 := hb (x (-5) 5)
    have b19296 := hb (x (-4) 4)
    have b19297 := hb (x (-3) 11)
    have b19298 := hb (x (-2) 10)
    have b19299 := hb (x (-1) 9)
    have b19300 := hb (x 0 8)
    clear * - r19286 e19287 e19288 e19289 e19290 e19291 e19292 b19293 b19294 b19295 b19296 b19297 b19298 b19299 b19300 g2 d19241 d19261
    omega
  have d19301 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
    have r19302 := hand2 (x (-3) 1) (x (-3) 11)
    have b19303 := hb (x (-3) 11)
    have b19304 := hb (x (-3) 1 && x (-3) 11)
    clear * - r19302 b19303 b19304 d19285
    omega
  have d19305 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
    have r19306 := hand2 (x (-3) 2) (x (-3) 11)
    have b19307 := hb (x (-3) 11)
    have b19308 := hb (x (-3) 2 && x (-3) 11)
    clear * - r19306 b19307 b19308 d19285
    omega
  have d19309 : (x (-3) 6 && x (-3) 11).toNat = 0 := by
    have r19310 := hand2 (x (-3) 6) (x (-3) 11)
    have b19311 := hb (x (-3) 11)
    have b19312 := hb (x (-3) 6 && x (-3) 11)
    clear * - r19310 b19311 b19312 d19285
    omega
  have d19313 : (x (-4) 4).toNat = 0 := by
    have r19314 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19315 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e19316 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e19317 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e19318 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e19319 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e19320 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b19321 := hb (x (-7) 7)
    have b19322 := hb (x (-6) 6)
    have b19323 := hb (x (-5) 5)
    have b19324 := hb (x (-4) 4)
    have b19325 := hb (x (-3) 11)
    have b19326 := hb (x (-2) 10)
    have b19327 := hb (x (-1) 9)
    have b19328 := hb (x 0 8)
    clear * - r19314 e19315 e19316 e19317 e19318 e19319 e19320 b19321 b19322 b19323 b19324 b19325 b19326 b19327 b19328 g2 d19241 d19261 d19285
    omega
  have d19329 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
    have r19330 := hand1 (x (-4) 4) (x (-4) 14)
    have b19331 := hb (x (-4) 4)
    have b19332 := hb (x (-4) 4 && x (-4) 14)
    clear * - r19330 b19331 b19332 d19313
    omega
  have d19333 : (x (-4) 4 && x (-4) 10).toNat = 0 := by
    have r19334 := hand1 (x (-4) 4) (x (-4) 10)
    have b19335 := hb (x (-4) 4)
    have b19336 := hb (x (-4) 4 && x (-4) 10)
    clear * - r19334 b19335 b19336 d19313
    omega
  have d19337 : (x (-4) 4 && x (-4) 8).toNat = 0 := by
    have r19338 := hand1 (x (-4) 4) (x (-4) 8)
    have b19339 := hb (x (-4) 4)
    have b19340 := hb (x (-4) 4 && x (-4) 8)
    clear * - r19338 b19339 b19340 d19313
    omega
  have d19341 : (x (-5) 5).toNat = 0 := by
    have r19342 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19343 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e19344 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e19345 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e19346 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e19347 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e19348 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b19349 := hb (x (-7) 7)
    have b19350 := hb (x (-6) 6)
    have b19351 := hb (x (-5) 5)
    have b19352 := hb (x (-4) 4)
    have b19353 := hb (x (-3) 11)
    have b19354 := hb (x (-2) 10)
    have b19355 := hb (x (-1) 9)
    have b19356 := hb (x 0 8)
    clear * - r19342 e19343 e19344 e19345 e19346 e19347 e19348 b19349 b19350 b19351 b19352 b19353 b19354 b19355 b19356 g2 d19241 d19261 d19285 d19313
    omega
  have d19357 : (x (-5) 5 && x (-5) 11).toNat = 0 := by
    have r19358 := hand1 (x (-5) 5) (x (-5) 11)
    have b19359 := hb (x (-5) 5)
    have b19360 := hb (x (-5) 5 && x (-5) 11)
    clear * - r19358 b19359 b19360 d19341
    omega
  have d19361 : (x (-5) 5 && x (-5) 9).toNat = 0 := by
    have r19362 := hand1 (x (-5) 5) (x (-5) 9)
    have b19363 := hb (x (-5) 5)
    have b19364 := hb (x (-5) 5 && x (-5) 9)
    clear * - r19362 b19363 b19364 d19341
    omega
  have d19365 : (x (-6) 6).toNat = 0 := by
    have r19366 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19367 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e19368 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e19369 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e19370 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e19371 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e19372 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b19373 := hb (x (-7) 7)
    have b19374 := hb (x (-6) 6)
    have b19375 := hb (x (-5) 5)
    have b19376 := hb (x (-4) 4)
    have b19377 := hb (x (-3) 11)
    have b19378 := hb (x (-2) 10)
    have b19379 := hb (x (-1) 9)
    have b19380 := hb (x 0 8)
    clear * - r19366 e19367 e19368 e19369 e19370 e19371 e19372 b19373 b19374 b19375 b19376 b19377 b19378 b19379 b19380 g2 d19241 d19261 d19285 d19313 d19341
    omega
  have d19381 : (x (-6) 6 && x (-6) 12).toNat = 0 := by
    have r19382 := hand1 (x (-6) 6) (x (-6) 12)
    have b19383 := hb (x (-6) 6)
    have b19384 := hb (x (-6) 6 && x (-6) 12)
    clear * - r19382 b19383 b19384 d19365
    omega
  have d19385 : (x (-6) 6 && x (-6) 10).toNat = 0 := by
    have r19386 := hand1 (x (-6) 6) (x (-6) 10)
    have b19387 := hb (x (-6) 6)
    have b19388 := hb (x (-6) 6 && x (-6) 10)
    clear * - r19386 b19387 b19388 d19365
    omega
  have d19389 : (x (-7) 7).toNat = 0 := by
    have r19390 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19391 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e19392 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e19393 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e19394 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e19395 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e19396 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b19397 := hb (x (-7) 7)
    have b19398 := hb (x (-6) 6)
    have b19399 := hb (x (-5) 5)
    have b19400 := hb (x (-4) 4)
    have b19401 := hb (x (-3) 11)
    have b19402 := hb (x (-2) 10)
    have b19403 := hb (x (-1) 9)
    have b19404 := hb (x 0 8)
    clear * - r19390 e19391 e19392 e19393 e19394 e19395 e19396 b19397 b19398 b19399 b19400 b19401 b19402 b19403 b19404 g2 d19241 d19261 d19285 d19313 d19341 d19365
    omega
  have d19405 : (x (-7) 7 && x (-7) 13).toNat = 0 := by
    have r19406 := hand1 (x (-7) 7) (x (-7) 13)
    have b19407 := hb (x (-7) 7)
    have b19408 := hb (x (-7) 7 && x (-7) 13)
    clear * - r19406 b19407 b19408 d19389
    omega
  have d19409 : (x (-7) 7 && x (-7) 11).toNat = 0 := by
    have r19410 := hand1 (x (-7) 7) (x (-7) 11)
    have b19411 := hb (x (-7) 7)
    have b19412 := hb (x (-7) 7 && x (-7) 11)
    clear * - r19410 b19411 b19412 d19389
    omega
  cases h19413 : x 0 2
  · have f19414 : (x 0 2).toNat = 0 := by rw [h19413]; rfl
    have d19415 : (x 0 10).toNat = 0 := by
      have r19416 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
      have b19417 := hb (x 0 2)
      have b19418 := hb (x 0 10)
      clear * - r19416 b19417 b19418 f19414
      omega
    have d19419 : (x 2 13).toNat = 1 := by
      have r19420 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b19421 := hb (x 0 2)
      have b19422 := hb (x 2 13)
      have b19423 := hb (x 1 1 && x 1 14)
      clear * - r19420 b19421 b19422 b19423 g30 f19414
      omega
    have d19424 : (x 2 1).toNat = 1 := by
      have r19425 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
      have b19426 := hb (x 2 1)
      have b19427 := hb (x 2 13)
      clear * - r19425 b19426 b19427 d19419
      omega
    have d19428 : (x 3 14).toNat = 0 := by
      have r19429 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b19430 := hb (x 2 1)
      have b19431 := hb (x 3 14)
      clear * - r19429 b19430 b19431 d19424
      omega
    have d19432 : (x 3 1 && x 3 14).toNat = 0 := by
      have r19433 := hand2 (x 3 1) (x 3 14)
      have b19434 := hb (x 3 14)
      have b19435 := hb (x 3 1 && x 3 14)
      clear * - r19433 b19434 b19435 d19428
      omega
    have d19436 : (x 3 6).toNat = 0 := by
      have r19437 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
      have b19438 := hb (x 3 6)
      have b19439 := hb (x 3 14)
      clear * - r19437 b19438 b19439 d19428
      omega
    have d19440 : (x 3 2 && x 3 6).toNat = 0 := by
      have r19441 := hand2 (x 3 2) (x 3 6)
      have b19442 := hb (x 3 6)
      have b19443 := hb (x 3 2 && x 3 6)
      clear * - r19441 b19442 b19443 d19436
      omega
    have d19444 : (x 3 2).toNat = 0 := by
      have r19445 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b19446 := hb (x 3 2)
      have b19447 := hb (x 3 14)
      clear * - r19445 b19446 b19447 d19428
      omega
    have d19448 : (x 3 2 && x 3 12).toNat = 0 := by
      have r19449 := hand1 (x 3 2) (x 3 12)
      have b19450 := hb (x 3 2)
      have b19451 := hb (x 3 2 && x 3 12)
      clear * - r19449 b19450 b19451 d19444
      omega
    have d19452 : (x 3 10).toNat = 0 := by
      have r19453 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
      have b19454 := hb (x 3 2)
      have b19455 := hb (x 3 10)
      clear * - r19453 b19454 b19455 d19444
      omega
    have d19456 : (x 3 12).toNat = 0 := by
      have r19457 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19458 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e19459 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b19460 := hb (x 0 3)
      have b19461 := hb (x 1 2)
      have b19462 := hb (x 2 13)
      have b19463 := hb (x 3 12)
      clear * - r19457 e19458 e19459 b19460 b19461 b19462 b19463 d19419 g4
      omega
    have d19464 : (x 3 3 && x 3 12).toNat = 0 := by
      have r19465 := hand2 (x 3 3) (x 3 12)
      have b19466 := hb (x 3 12)
      have b19467 := hb (x 3 3 && x 3 12)
      clear * - r19465 b19466 b19467 d19456
      omega
    have d19468 : (x 0 3).toNat = 0 := by
      have r19469 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19470 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e19471 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b19472 := hb (x 0 3)
      have b19473 := hb (x 1 2)
      have b19474 := hb (x 2 13)
      have b19475 := hb (x 3 12)
      clear * - r19469 e19470 e19471 b19472 b19473 b19474 b19475 d19456 d19419 g4
      omega
    have d19476 : (x 0 3 && x 0 12).toNat = 0 := by
      have r19477 := hand1 (x 0 3) (x 0 12)
      have b19478 := hb (x 0 3)
      have b19479 := hb (x 0 3 && x 0 12)
      clear * - r19477 b19478 b19479 d19468
      omega
    have d19480 : (x 0 3 && x 0 8).toNat = 0 := by
      have r19481 := hand1 (x 0 3) (x 0 8)
      have b19482 := hb (x 0 3)
      have b19483 := hb (x 0 3 && x 0 8)
      clear * - r19481 b19482 b19483 d19468
      omega
    have d19484 : (x 0 11).toNat = 0 := by
      have r19485 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
      have b19486 := hb (x 0 3)
      have b19487 := hb (x 0 11)
      clear * - r19485 b19486 b19487 d19468
      omega
    have d19488 : (x 0 1 && x 0 11).toNat = 0 := by
      have r19489 := hand2 (x 0 1) (x 0 11)
      have b19490 := hb (x 0 11)
      have b19491 := hb (x 0 1 && x 0 11)
      clear * - r19489 b19490 b19491 d19484
      omega
    have d19492 : (x 2 3 && x 2 13).toNat = 1 := by
      have r19493 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b19494 := hb (x 0 5)
      have b19495 := hb (x 5 10)
      have b19496 := hb (x 4 1 && x 4 11)
      have b19497 := hb (x 3 2 && x 3 12)
      have b19498 := hb (x 2 3 && x 2 13)
      have b19499 := hb (x 1 4 && x 1 14)
      clear * - r19493 b19494 b19495 b19496 b19497 b19498 b19499 g10 g26 d19448 g27 g0
      omega
    have d19500 : (x 2 3).toNat = 1 := by
      have r19501 := hand1 (x 2 3) (x 2 13)
      have b19502 := hb (x 2 3)
      have b19503 := hb (x 2 3 && x 2 13)
      clear * - r19501 b19502 b19503 d19492
      omega
    have d19504 : (x 5 12).toNat = 0 := by
      have r19505 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19506 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e19507 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b19508 := hb (x 2 3)
      have b19509 := hb (x 3 2)
      have b19510 := hb (x 4 13)
      have b19511 := hb (x 5 12)
      clear * - r19505 e19506 e19507 b19508 b19509 b19510 b19511 d19444 d19500
      omega
    have d19512 : (x 5 2 && x 5 12).toNat = 0 := by
      have r19513 := hand2 (x 5 2) (x 5 12)
      have b19514 := hb (x 5 12)
      have b19515 := hb (x 5 2 && x 5 12)
      clear * - r19513 b19514 b19515 d19504
      omega
    have d19516 : (x 5 4).toNat = 0 := by
      have r19517 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
      have b19518 := hb (x 5 4)
      have b19519 := hb (x 5 12)
      clear * - r19517 b19518 b19519 d19504
      omega
    have d19520 : (x 4 13).toNat = 0 := by
      have r19521 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19522 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e19523 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b19524 := hb (x 2 3)
      have b19525 := hb (x 3 2)
      have b19526 := hb (x 4 13)
      have b19527 := hb (x 5 12)
      clear * - r19521 e19522 e19523 b19524 b19525 b19526 b19527 d19504 d19444 d19500
      omega
    have d19528 : (x 4 3 && x 4 13).toNat = 0 := by
      have r19529 := hand2 (x 4 3) (x 4 13)
      have b19530 := hb (x 4 13)
      have b19531 := hb (x 4 3 && x 4 13)
      clear * - r19529 b19530 b19531 d19520
      omega
    have d19532 : (x 4 5).toNat = 0 := by
      have r19533 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
      have b19534 := hb (x 4 5)
      have b19535 := hb (x 4 13)
      clear * - r19533 b19534 b19535 d19520
      omega
    have d19536 : (x 2 2).toNat = 1 := by
      have r19537 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b19538 := hb (x 2 2)
      have b19539 := hb (x 4 13)
      have b19540 := hb (x 3 1 && x 3 14)
      clear * - r19537 b19538 b19539 b19540 d19520 d19432
      omega
    have d19541 : (x 2 14).toNat = 1 := by
      have r19542 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b19543 := hb (x 2 2)
      have b19544 := hb (x 2 14)
      clear * - r19542 b19543 b19544 d19536
      omega
    have d19545 : (x 1 1).toNat = 0 := by
      have r19546 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b19547 := hb (x 1 1)
      have b19548 := hb (x 2 14)
      clear * - r19546 b19547 b19548 d19541
      omega
    have d19549 : (x 1 13).toNat = 0 := by
      have r19550 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
      have b19551 := hb (x 1 1)
      have b19552 := hb (x 1 13)
      clear * - r19550 b19551 b19552 d19545
      omega
    have d19553 : (x 1 7 && x 1 13).toNat = 0 := by
      have r19554 := hand2 (x 1 7) (x 1 13)
      have b19555 := hb (x 1 13)
      have b19556 := hb (x 1 7 && x 1 13)
      clear * - r19554 b19555 b19556 d19549
      omega
    have d19557 : (x 1 5).toNat = 0 := by
      have r19558 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
      have b19559 := hb (x 1 5)
      have b19560 := hb (x 1 13)
      clear * - r19558 b19559 b19560 d19549
      omega
    have d19561 : (x 4 12).toNat = 0 := by
      have r19562 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19563 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e19564 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b19565 := hb (x 1 3)
      have b19566 := hb (x 2 2)
      have b19567 := hb (x 3 13)
      have b19568 := hb (x 4 12)
      clear * - r19562 e19563 e19564 b19565 b19566 b19567 b19568 d19536
      omega
    have d19569 : (x 4 3 && x 4 12).toNat = 0 := by
      have r19570 := hand2 (x 4 3) (x 4 12)
      have b19571 := hb (x 4 12)
      have b19572 := hb (x 4 3 && x 4 12)
      clear * - r19570 b19571 b19572 d19561
      omega
    have d19573 : (x 4 4).toNat = 0 := by
      have r19574 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
      have b19575 := hb (x 4 4)
      have b19576 := hb (x 4 12)
      clear * - r19574 b19575 b19576 d19561
      omega
    have d19577 : (x 4 4 && x 4 10).toNat = 0 := by
      have r19578 := hand1 (x 4 4) (x 4 10)
      have b19579 := hb (x 4 4)
      have b19580 := hb (x 4 4 && x 4 10)
      clear * - r19578 b19579 b19580 d19573
      omega
    have d19581 : (x 3 13).toNat = 0 := by
      have r19582 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19583 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e19584 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b19585 := hb (x 1 3)
      have b19586 := hb (x 2 2)
      have b19587 := hb (x 3 13)
      have b19588 := hb (x 4 12)
      clear * - r19582 e19583 e19584 b19585 b19586 b19587 b19588 d19561 d19536
      omega
    have d19589 : (x 3 5).toNat = 0 := by
      have r19590 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
      have b19591 := hb (x 3 5)
      have b19592 := hb (x 3 13)
      clear * - r19590 b19591 b19592 d19581
      omega
    have d19593 : (x 3 5 && x 3 11).toNat = 0 := by
      have r19594 := hand1 (x 3 5) (x 3 11)
      have b19595 := hb (x 3 5)
      have b19596 := hb (x 3 5 && x 3 11)
      clear * - r19594 b19595 b19596 d19589
      omega
    have d19597 : (x 1 3).toNat = 0 := by
      have r19598 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19599 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e19600 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b19601 := hb (x 1 3)
      have b19602 := hb (x 2 2)
      have b19603 := hb (x 3 13)
      have b19604 := hb (x 4 12)
      clear * - r19598 e19599 e19600 b19601 b19602 b19603 b19604 d19561 d19581 d19536
      omega
    have d19605 : (x 1 11).toNat = 0 := by
      have r19606 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
      have b19607 := hb (x 1 3)
      have b19608 := hb (x 1 11)
      clear * - r19606 b19607 b19608 d19597
      omega
    have d19609 : (x 2 4 && x 2 13).toNat = 1 := by
      have r19610 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b19611 := hb (x 0 6)
      have b19612 := hb (x 6 9)
      have b19613 := hb (x 5 1 && x 5 10)
      have b19614 := hb (x 4 2 && x 4 11)
      have b19615 := hb (x 3 3 && x 3 12)
      have b19616 := hb (x 2 4 && x 2 13)
      have b19617 := hb (x 1 5 && x 1 14)
      clear * - r19610 b19611 b19612 b19613 b19614 b19615 b19616 b19617 g11 g19 g20 d19464 g21 g1
      omega
    have d19618 : (x 2 4).toNat = 1 := by
      have r19619 := hand1 (x 2 4) (x 2 13)
      have b19620 := hb (x 2 4)
      have b19621 := hb (x 2 4 && x 2 13)
      clear * - r19619 b19620 b19621 d19609
      omega
    have d19622 : (x 2 12).toNat = 1 := by
      have r19623 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
      have b19624 := hb (x 2 4)
      have b19625 := hb (x 2 12)
      clear * - r19623 b19624 b19625 d19618
      omega
    have d19626 : (x (-1) 3).toNat = 0 := by
      have r19627 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19628 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e19629 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b19630 := hb (x (-1) 3)
      have b19631 := hb (x 0 2)
      have b19632 := hb (x 1 13)
      have b19633 := hb (x 2 12)
      clear * - r19627 e19628 e19629 b19630 b19631 b19632 b19633 d19622 d19549 f19414
      omega
    have d19634 : (x (-1) 11).toNat = 0 := by
      have r19635 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b19636 := hb (x (-1) 3)
      have b19637 := hb (x (-1) 11)
      clear * - r19635 b19636 b19637 d19626
      omega
    have d19638 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
      have r19639 := hand2 (x (-1) 1) (x (-1) 11)
      have b19640 := hb (x (-1) 11)
      have b19641 := hb (x (-1) 1 && x (-1) 11)
      clear * - r19639 b19640 b19641 d19634
      omega
    have d19642 : (x 6 8).toNat = 0 := by
      have r19643 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19644 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e19645 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e19646 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e19647 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e19648 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e19649 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b19650 := hb (x (-1) 7)
      have b19651 := hb (x 0 6)
      have b19652 := hb (x 1 5)
      have b19653 := hb (x 2 4)
      have b19654 := hb (x 3 11)
      have b19655 := hb (x 4 10)
      have b19656 := hb (x 5 9)
      have b19657 := hb (x 6 8)
      clear * - r19643 e19644 e19645 e19646 e19647 e19648 e19649 b19650 b19651 b19652 b19653 b19654 b19655 b19656 b19657 d19618 d19557 g1
      omega
    have d19658 : (x 6 1 && x 6 8).toNat = 0 := by
      have r19659 := hand2 (x 6 1) (x 6 8)
      have b19660 := hb (x 6 8)
      have b19661 := hb (x 6 1 && x 6 8)
      clear * - r19659 b19660 b19661 d19642
      omega
    have d19662 : (x 6 2 && x 6 8).toNat = 0 := by
      have r19663 := hand2 (x 6 2) (x 6 8)
      have b19664 := hb (x 6 8)
      have b19665 := hb (x 6 2 && x 6 8)
      clear * - r19663 b19664 b19665 d19642
      omega
    have d19666 : (x 5 9).toNat = 0 := by
      have r19667 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19668 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e19669 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e19670 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e19671 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e19672 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e19673 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b19674 := hb (x (-1) 7)
      have b19675 := hb (x 0 6)
      have b19676 := hb (x 1 5)
      have b19677 := hb (x 2 4)
      have b19678 := hb (x 3 11)
      have b19679 := hb (x 4 10)
      have b19680 := hb (x 5 9)
      have b19681 := hb (x 6 8)
      clear * - r19667 e19668 e19669 e19670 e19671 e19672 e19673 b19674 b19675 b19676 b19677 b19678 b19679 b19680 b19681 d19642 d19618 d19557 g1
      omega
    have d19682 : (x 5 2 && x 5 9).toNat = 0 := by
      have r19683 := hand2 (x 5 2) (x 5 9)
      have b19684 := hb (x 5 9)
      have b19685 := hb (x 5 2 && x 5 9)
      clear * - r19683 b19684 b19685 d19666
      omega
    have d19686 : (x 5 3 && x 5 9).toNat = 0 := by
      have r19687 := hand2 (x 5 3) (x 5 9)
      have b19688 := hb (x 5 9)
      have b19689 := hb (x 5 3 && x 5 9)
      clear * - r19687 b19688 b19689 d19666
      omega
    have d19690 : (x 4 10).toNat = 0 := by
      have r19691 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19692 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e19693 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e19694 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e19695 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e19696 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e19697 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b19698 := hb (x (-1) 7)
      have b19699 := hb (x 0 6)
      have b19700 := hb (x 1 5)
      have b19701 := hb (x 2 4)
      have b19702 := hb (x 3 11)
      have b19703 := hb (x 4 10)
      have b19704 := hb (x 5 9)
      have b19705 := hb (x 6 8)
      clear * - r19691 e19692 e19693 e19694 e19695 e19696 e19697 b19698 b19699 b19700 b19701 b19702 b19703 b19704 b19705 d19642 d19666 d19618 d19557 g1
      omega
    have d19706 : (x 4 3 && x 4 10).toNat = 0 := by
      have r19707 := hand2 (x 4 3) (x 4 10)
      have b19708 := hb (x 4 10)
      have b19709 := hb (x 4 3 && x 4 10)
      clear * - r19707 b19708 b19709 d19690
      omega
    have d19710 : (x 3 11).toNat = 0 := by
      have r19711 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19712 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e19713 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e19714 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e19715 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e19716 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e19717 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b19718 := hb (x (-1) 7)
      have b19719 := hb (x 0 6)
      have b19720 := hb (x 1 5)
      have b19721 := hb (x 2 4)
      have b19722 := hb (x 3 11)
      have b19723 := hb (x 4 10)
      have b19724 := hb (x 5 9)
      have b19725 := hb (x 6 8)
      clear * - r19711 e19712 e19713 e19714 e19715 e19716 e19717 b19718 b19719 b19720 b19721 b19722 b19723 b19724 b19725 d19642 d19666 d19690 d19618 d19557 g1
      omega
    have d19726 : (x (-1) 7).toNat = 0 := by
      have r19727 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19728 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e19729 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e19730 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e19731 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e19732 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e19733 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b19734 := hb (x (-1) 7)
      have b19735 := hb (x 0 6)
      have b19736 := hb (x 1 5)
      have b19737 := hb (x 2 4)
      have b19738 := hb (x 3 11)
      have b19739 := hb (x 4 10)
      have b19740 := hb (x 5 9)
      have b19741 := hb (x 6 8)
      clear * - r19727 e19728 e19729 e19730 e19731 e19732 e19733 b19734 b19735 b19736 b19737 b19738 b19739 b19740 b19741 d19642 d19666 d19690 d19710 d19618 d19557 g1
      omega
    have d19742 : (x (-1) 1 && x (-1) 7).toNat = 0 := by
      have r19743 := hand2 (x (-1) 1) (x (-1) 7)
      have b19744 := hb (x (-1) 7)
      have b19745 := hb (x (-1) 1 && x (-1) 7)
      clear * - r19743 b19744 b19745 d19726
      omega
    cases h19746 : x 0 4
    · have f19747 : (x 0 4).toNat = 0 := by rw [h19746]; rfl
      cases h19748 : x 0 12
      · have f19749 : (x 0 12).toNat = 0 := by rw [h19748]; rfl
        have d19750 : (x 0 1 && x 0 12).toNat = 0 := by
          have r19751 := hand2 (x 0 1) (x 0 12)
          have b19752 := hb (x 0 12)
          have b19753 := hb (x 0 1 && x 0 12)
          clear * - r19751 b19752 b19753 f19749
          omega
        cases h19754 : x 1 4
        · have f19755 : (x 1 4).toNat = 0 := by rw [h19754]; rfl
          have d19756 : (x 1 4 && x 1 8).toNat = 0 := by
            have r19757 := hand1 (x 1 4) (x 1 8)
            have b19758 := hb (x 1 4)
            have b19759 := hb (x 1 4 && x 1 8)
            clear * - r19757 b19758 b19759 f19755
            omega
          cases h19760 : x (-1) 6
          · have f19761 : (x (-1) 6).toNat = 0 := by rw [h19760]; rfl
            have d19762 : (x (-1) 6 && x (-1) 10).toNat = 0 := by
              have r19763 := hand1 (x (-1) 6) (x (-1) 10)
              have b19764 := hb (x (-1) 6)
              have b19765 := hb (x (-1) 6 && x (-1) 10)
              clear * - r19763 b19764 b19765 f19761
              omega
            cases h19766 : x 1 7
            · have f19767 : (x 1 7).toNat = 0 := by rw [h19766]; rfl
              cases h19768 : x (-1) 8
              · have f19769 : (x (-1) 8).toNat = 0 := by rw [h19768]; rfl
                cases h19770 : x (-1) 12
                · have f19771 : (x (-1) 12).toNat = 0 := by rw [h19770]; rfl
                  have d19772 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
                    have r19773 := hand2 (x (-1) 1) (x (-1) 12)
                    have b19774 := hb (x (-1) 12)
                    have b19775 := hb (x (-1) 1 && x (-1) 12)
                    clear * - r19773 b19774 b19775 f19771
                    omega
                  have d19776 : (x (-1) 4).toNat = 0 := by
                    have r19777 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                    have b19778 := hb (x (-1) 4)
                    have b19779 := hb (x (-1) 12)
                    clear * - r19777 b19778 b19779 f19771
                    omega
                  have d19780 : (x (-1) 4 && x (-1) 13).toNat = 0 := by
                    have r19781 := hand1 (x (-1) 4) (x (-1) 13)
                    have b19782 := hb (x (-1) 4)
                    have b19783 := hb (x (-1) 4 && x (-1) 13)
                    clear * - r19781 b19782 b19783 d19776
                    omega
                  cases h19784 : x (-1) 13
                  · have f19785 : (x (-1) 13).toNat = 0 := by rw [h19784]; rfl
                    have d19786 : (x (-1) 2 && x (-1) 13).toNat = 0 := by
                      have r19787 := hand2 (x (-1) 2) (x (-1) 13)
                      have b19788 := hb (x (-1) 13)
                      have b19789 := hb (x (-1) 2 && x (-1) 13)
                      clear * - r19787 b19788 b19789 f19785
                      omega
                    have d19790 : (x (-1) 5).toNat = 0 := by
                      have r19791 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
                      have b19792 := hb (x (-1) 5)
                      have b19793 := hb (x (-1) 13)
                      clear * - r19791 b19792 b19793 f19785
                      omega
                    cases h19794 : x (-1) 14
                    · have f19795 : (x (-1) 14).toNat = 0 := by rw [h19794]; rfl
                      have d19796 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
                        have r19797 := hand2 (x (-1) 1) (x (-1) 14)
                        have b19798 := hb (x (-1) 14)
                        have b19799 := hb (x (-1) 1 && x (-1) 14)
                        clear * - r19797 b19798 b19799 f19795
                        omega
                      have d19800 : (x (-2) 2).toNat = 1 := by
                        have r19801 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b19802 := hb (x (-2) 2)
                        have b19803 := hb (x 0 13)
                        have b19804 := hb (x (-1) 1 && x (-1) 14)
                        clear * - r19801 b19802 b19803 b19804 g3 d19796
                        omega
                      have d19805 : (x (-2) 14).toNat = 1 := by
                        have r19806 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
                        have b19807 := hb (x (-2) 2)
                        have b19808 := hb (x (-2) 14)
                        clear * - r19806 b19807 b19808 d19800
                        omega
                      have d19809 : (x (-3) 1).toNat = 0 := by
                        have r19810 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b19811 := hb (x (-3) 1)
                        have b19812 := hb (x (-2) 14)
                        clear * - r19810 b19811 b19812 d19805
                        omega
                      have d19813 : (x (-3) 13).toNat = 0 := by
                        have r19814 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                        have b19815 := hb (x (-3) 1)
                        have b19816 := hb (x (-3) 13)
                        clear * - r19814 b19815 b19816 d19809
                        omega
                      have d19817 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
                        have r19818 := hand2 (x (-3) 3) (x (-3) 13)
                        have b19819 := hb (x (-3) 13)
                        have b19820 := hb (x (-3) 3 && x (-3) 13)
                        clear * - r19818 b19819 b19820 d19813
                        omega
                      have d19821 : (x (-3) 9).toNat = 0 := by
                        have r19822 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
                        have b19823 := hb (x (-3) 1)
                        have b19824 := hb (x (-3) 9)
                        clear * - r19822 b19823 b19824 d19809
                        omega
                      have d19825 : (x (-3) 3 && x (-3) 9).toNat = 0 := by
                        have r19826 := hand2 (x (-3) 3) (x (-3) 9)
                        have b19827 := hb (x (-3) 9)
                        have b19828 := hb (x (-3) 3 && x (-3) 9)
                        clear * - r19826 b19827 b19828 d19821
                        omega
                      have d19829 : (x (-3) 3).toNat = 0 := by
                        have r19830 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e19831 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                        have e19832 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                        have b19833 := hb (x (-3) 3)
                        have b19834 := hb (x (-2) 2)
                        have b19835 := hb (x (-1) 13)
                        have b19836 := hb (x 0 12)
                        clear * - r19830 e19831 e19832 b19833 b19834 b19835 b19836 f19749 f19785 d19800
                        omega
                      have d19837 : (x (-3) 3 && x (-3) 7).toNat = 0 := by
                        have r19838 := hand1 (x (-3) 3) (x (-3) 7)
                        have b19839 := hb (x (-3) 3)
                        have b19840 := hb (x (-3) 3 && x (-3) 7)
                        clear * - r19838 b19839 b19840 d19829
                        omega
                      have d19841 : (x (-2) 2 && x (-2) 12).toNat = 1 := by
                        have r19842 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b19843 := hb (x (-5) 5)
                        have b19844 := hb (x 0 10)
                        have b19845 := hb (x (-1) 1 && x (-1) 11)
                        have b19846 := hb (x (-2) 2 && x (-2) 12)
                        have b19847 := hb (x (-3) 3 && x (-3) 13)
                        have b19848 := hb (x (-4) 4 && x (-4) 14)
                        clear * - r19842 b19843 b19844 b19845 b19846 b19847 b19848 d19415 d19638 d19817 d19329 d19341
                        omega
                      have d19849 : (x (-2) 12).toNat = 1 := by
                        have r19850 := hand2 (x (-2) 2) (x (-2) 12)
                        have b19851 := hb (x (-2) 12)
                        have b19852 := hb (x (-2) 2 && x (-2) 12)
                        clear * - r19850 b19851 b19852 d19841
                        omega
                      have d19853 : (x (-4) 2).toNat = 0 := by
                        have r19854 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e19855 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                        have e19856 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                        have b19857 := hb (x (-5) 3)
                        have b19858 := hb (x (-4) 2)
                        have b19859 := hb (x (-3) 13)
                        have b19860 := hb (x (-2) 12)
                        clear * - r19854 e19855 e19856 b19857 b19858 b19859 b19860 d19849 d19813
                        omega
                      have d19861 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
                        have r19862 := hand1 (x (-4) 2) (x (-4) 12)
                        have b19863 := hb (x (-4) 2)
                        have b19864 := hb (x (-4) 2 && x (-4) 12)
                        clear * - r19862 b19863 b19864 d19853
                        omega
                      have d19865 : (x (-4) 10).toNat = 0 := by
                        have r19866 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
                        have b19867 := hb (x (-4) 2)
                        have b19868 := hb (x (-4) 10)
                        clear * - r19866 b19867 b19868 d19853
                        omega
                      have d19869 : (x (-5) 3).toNat = 0 := by
                        have r19870 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e19871 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                        have e19872 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                        have b19873 := hb (x (-5) 3)
                        have b19874 := hb (x (-4) 2)
                        have b19875 := hb (x (-3) 13)
                        have b19876 := hb (x (-2) 12)
                        clear * - r19870 e19871 e19872 b19873 b19874 b19875 b19876 d19849 d19813 d19853
                        omega
                      have d19877 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
                        have r19878 := hand1 (x (-5) 3) (x (-5) 13)
                        have b19879 := hb (x (-5) 3)
                        have b19880 := hb (x (-5) 3 && x (-5) 13)
                        clear * - r19878 b19879 b19880 d19869
                        omega
                      have d19881 : (x (-5) 11).toNat = 0 := by
                        have r19882 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
                        have b19883 := hb (x (-5) 3)
                        have b19884 := hb (x (-5) 11)
                        clear * - r19882 b19883 b19884 d19869
                        omega
                      have r19885 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19886 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e19887 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                      have e19888 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                      have e19889 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                      have e19890 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                      have e19891 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                      have e19892 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                      have r19893 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e19894 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
                      have e19895 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
                      have e19896 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
                      have e19897 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
                      have e19898 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
                      have e19899 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
                      have r19900 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e19901 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                      have e19902 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                      have e19903 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                      have e19904 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                      have e19905 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                      have e19906 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                      have r19907 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e19908 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                      have e19909 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                      have e19910 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                      have e19911 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                      have e19912 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                      have e19913 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                      have r19914 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e19915 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                      have e19916 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                      have r19917 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e19918 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
                      have e19919 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
                      have r19920 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e19921 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
                      have e19922 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
                      have r19923 : 1 ≤ (x 3 5).toNat + (x 2 1 && x 2 6).toNat + (x 1 2 && x 1 7).toNat + (x 0 3 && x 0 8).toNat + (x (-1) 4 && x (-1) 9).toNat + (x (-2) 5 && x (-2) 10).toNat + (x (-3) 6 && x (-3) 11).toNat + (x (-4) 7 && x (-4) 12).toNat + (x (-5) 8 && x (-5) 13).toNat + (x (-6) 9 && x (-6) 14).toNat + (x (-7) 10).toNat := by have q := hcov5 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19924 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19925 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19926 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19927 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19928 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19929 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have r19930 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
                      have r19931 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
                      have r19932 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
                      have r19933 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
                      have r19934 := hand2 (x (-2) 2) (x (-2) 6)
                      have r19935 := hand2 (x (-8) 8) (x (-8) 12)
                      have r19936 := hand2 (x (-9) 9) (x (-9) 13)
                      have r19937 := hand2 (x 2 1) (x 2 6)
                      have r19938 := hand1 (x (-4) 7) (x (-4) 12)
                      have r19939 := hand1 (x (-5) 8) (x (-5) 13)
                      have r19940 := hand1 (x (-6) 9) (x (-6) 14)
                      have r19941 := hand2 (x (-2) 2) (x (-2) 8)
                      have r19942 := hand1 (x (-8) 8) (x (-8) 14)
                      have r19943 := hand2 (x 2 1) (x 2 10)
                      have r19944 := hand1 (x (-2) 5) (x (-2) 14)
                      have r19945 := hand2 (x 6 1) (x 6 10)
                      have r19946 := hand2 (x 5 2) (x 5 11)
                      have r19947 := hand2 (x (-9) 1) (x (-9) 11)
                      have r19948 := hand1 (x (-10) 2) (x (-10) 12)
                      have r19949 := hand1 (x (-11) 3) (x (-11) 13)
                      have r19950 := hand1 (x (-12) 4) (x (-12) 14)
                      have r19951 := hand1 (x (-6) 4) (x (-6) 14)
                      have r19952 := hand2 (x (-9) 1) (x (-9) 12)
                      have r19953 := hand2 (x (-10) 2) (x (-10) 13)
                      have r19954 := hand2 (x (-11) 3) (x (-11) 14)
                      linarith only [r19885, r19886, e19887, e19888, e19889, e19890, e19891, e19892, r19893, e19894, e19895, e19896, e19897, e19898, e19899, r19900, e19901, e19902, e19903, e19904, e19905, e19906, r19907, e19908, e19909, e19910, e19911, e19912, e19913, r19914, e19915, e19916, r19917, e19918, e19919, r19920, e19921, e19922, r19923, r19924, r19925, r19926, r19927, r19928, r19929, r19930, r19931, r19932, r19933, r19934, r19935, r19936, r19937, r19938, r19939, r19940, r19941, r19942, r19943, r19944, r19945, r19946, r19947, r19948, r19949, r19950, r19951, r19952, r19953, r19954, d19881, d19865, d19821, d19261, d19776, d19790, d19468, f19747, g1, g4, g5, f19767, d19605, d19424, d19589, d19573, d19837, d19337, d19361, d19385, d19409, g14, d19480, d19257, d19281, d19309, d19742, d19825, d19333, d19357, d19381, d19405, g18, d19476, d19780, d19569, g22, g23, d19301, d19861, d19877]
                    · have f20060 : (x (-1) 14).toNat = 1 := by rw [h19794]; rfl
                      have d20061 : (x (-2) 1).toNat = 0 := by
                        have r20062 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20063 := hb (x (-2) 1)
                        have b20064 := hb (x (-1) 14)
                        clear * - r20062 b20063 b20064 f20060
                        omega
                      have d20065 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                        have r20066 := hand1 (x (-2) 1) (x (-2) 14)
                        have b20067 := hb (x (-2) 1)
                        have b20068 := hb (x (-2) 1 && x (-2) 14)
                        clear * - r20066 b20067 b20068 d20061
                        omega
                      have d20069 : (x (-2) 13).toNat = 0 := by
                        have r20070 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                        have b20071 := hb (x (-2) 1)
                        have b20072 := hb (x (-2) 13)
                        clear * - r20070 b20071 b20072 d20061
                        omega
                      have d20073 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
                        have r20074 := hand2 (x (-2) 2) (x (-2) 13)
                        have b20075 := hb (x (-2) 13)
                        have b20076 := hb (x (-2) 2 && x (-2) 13)
                        clear * - r20074 b20075 b20076 d20069
                        omega
                      have d20077 : (x (-3) 2).toNat = 1 := by
                        have r20078 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20079 := hb (x (-3) 2)
                        have b20080 := hb (x (-1) 13)
                        have b20081 := hb (x (-2) 1 && x (-2) 14)
                        clear * - r20078 b20079 b20080 b20081 f19785 d20065
                        omega
                      have d20082 : (x (-3) 14).toNat = 1 := by
                        have r20083 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
                        have b20084 := hb (x (-3) 2)
                        have b20085 := hb (x (-3) 14)
                        clear * - r20083 b20084 b20085 d20077
                        omega
                      have d20086 : (x (-4) 1).toNat = 0 := by
                        have r20087 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20088 := hb (x (-4) 1)
                        have b20089 := hb (x (-3) 14)
                        clear * - r20087 b20088 b20089 d20082
                        omega
                      have d20090 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
                        have r20091 := hand1 (x (-4) 1) (x (-4) 12)
                        have b20092 := hb (x (-4) 1)
                        have b20093 := hb (x (-4) 1 && x (-4) 12)
                        clear * - r20091 b20092 b20093 d20086
                        omega
                      have d20094 : (x (-4) 13).toNat = 0 := by
                        have r20095 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
                        have b20096 := hb (x (-4) 1)
                        have b20097 := hb (x (-4) 13)
                        clear * - r20095 b20096 b20097 d20086
                        omega
                      have d20098 : (x (-4) 9 && x (-4) 13).toNat = 0 := by
                        have r20099 := hand2 (x (-4) 9) (x (-4) 13)
                        have b20100 := hb (x (-4) 13)
                        have b20101 := hb (x (-4) 9 && x (-4) 13)
                        clear * - r20099 b20100 b20101 d20094
                        omega
                      have d20102 : (x (-4) 9).toNat = 0 := by
                        have r20103 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
                        have b20104 := hb (x (-4) 1)
                        have b20105 := hb (x (-4) 9)
                        clear * - r20103 b20104 b20105 d20086
                        omega
                      have d20106 : (x (-3) 3 && x (-3) 14).toNat = 1 := by
                        have r20107 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20108 := hb (x (-4) 4)
                        have b20109 := hb (x 0 11)
                        have b20110 := hb (x (-1) 1 && x (-1) 12)
                        have b20111 := hb (x (-2) 2 && x (-2) 13)
                        have b20112 := hb (x (-3) 3 && x (-3) 14)
                        clear * - r20107 b20108 b20109 b20110 b20111 b20112 d19484 d19772 d20073 d19313
                        omega
                      have d20113 : (x (-3) 3).toNat = 1 := by
                        have r20114 := hand1 (x (-3) 3) (x (-3) 14)
                        have b20115 := hb (x (-3) 3)
                        have b20116 := hb (x (-3) 3 && x (-3) 14)
                        clear * - r20114 b20115 b20116 d20106
                        omega
                      have d20117 : (x (-2) 2).toNat = 0 := by
                        have r20118 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20119 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                        have e20120 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                        have b20121 := hb (x (-3) 3)
                        have b20122 := hb (x (-2) 2)
                        have b20123 := hb (x (-1) 13)
                        have b20124 := hb (x 0 12)
                        clear * - r20118 e20119 e20120 b20121 b20122 b20123 b20124 f19749 f19785 d20113
                        omega
                      have d20125 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
                        have r20126 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20127 := hb (x (-2) 2)
                        have b20128 := hb (x 0 13)
                        have b20129 := hb (x (-1) 1 && x (-1) 14)
                        clear * - r20126 b20127 b20128 b20129 g3 d20117
                        omega
                      have d20130 : (x (-1) 1).toNat = 1 := by
                        have r20131 := hand1 (x (-1) 1) (x (-1) 14)
                        have b20132 := hb (x (-1) 1)
                        have b20133 := hb (x (-1) 1 && x (-1) 14)
                        clear * - r20131 b20132 b20133 d20125
                        omega
                      have d20134 : (x 0 14).toNat = 0 := by
                        have r20135 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20136 := hb (x (-1) 1)
                        have b20137 := hb (x 0 14)
                        clear * - r20135 b20136 b20137 d20130
                        omega
                      have d20138 : (x 0 1 && x 0 14).toNat = 0 := by
                        have r20139 := hand2 (x 0 1) (x 0 14)
                        have b20140 := hb (x 0 14)
                        have b20141 := hb (x 0 1 && x 0 14)
                        clear * - r20139 b20140 b20141 d20134
                        omega
                      have d20142 : (x (-1) 2).toNat = 1 := by
                        have r20143 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20144 := hb (x (-1) 2)
                        have b20145 := hb (x 1 13)
                        have b20146 := hb (x 0 1 && x 0 14)
                        clear * - r20143 b20144 b20145 b20146 d19549 d20138
                        omega
                      have d20147 : (x 1 12).toNat = 0 := by
                        have r20148 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20149 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                        have e20150 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                        have b20151 := hb (x (-2) 3)
                        have b20152 := hb (x (-1) 2)
                        have b20153 := hb (x 0 13)
                        have b20154 := hb (x 1 12)
                        clear * - r20148 e20149 e20150 b20151 b20152 b20153 b20154 g3 d20142
                        omega
                      have d20155 : (x (-2) 3).toNat = 0 := by
                        have r20156 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20157 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                        have e20158 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                        have b20159 := hb (x (-2) 3)
                        have b20160 := hb (x (-1) 2)
                        have b20161 := hb (x 0 13)
                        have b20162 := hb (x 1 12)
                        clear * - r20156 e20157 e20158 b20159 b20160 b20161 b20162 d20147 g3 d20142
                        omega
                      have d20163 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
                        have r20164 := hand1 (x (-2) 3) (x (-2) 14)
                        have b20165 := hb (x (-2) 3)
                        have b20166 := hb (x (-2) 3 && x (-2) 14)
                        clear * - r20164 b20165 b20166 d20155
                        omega
                      have d20167 : (x (-3) 4).toNat = 1 := by
                        have r20168 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20169 := hb (x (-3) 4)
                        have b20170 := hb (x 1 11)
                        have b20171 := hb (x 0 1 && x 0 12)
                        have b20172 := hb (x (-1) 2 && x (-1) 13)
                        have b20173 := hb (x (-2) 3 && x (-2) 14)
                        clear * - r20168 b20169 b20170 b20171 b20172 b20173 d19605 d19750 d19786 d20163
                        omega
                      have d20174 : (x (-3) 12).toNat = 1 := by
                        have r20175 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
                        have b20176 := hb (x (-3) 4)
                        have b20177 := hb (x (-3) 12)
                        clear * - r20175 b20176 b20177 d20167
                        omega
                      have d20178 : (x (-5) 2).toNat = 0 := by
                        have r20179 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20180 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                        have e20181 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                        have b20182 := hb (x (-6) 3)
                        have b20183 := hb (x (-5) 2)
                        have b20184 := hb (x (-4) 13)
                        have b20185 := hb (x (-3) 12)
                        clear * - r20179 e20180 e20181 b20182 b20183 b20184 b20185 d20174 d20094
                        omega
                      have d20186 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
                        have r20187 := hand1 (x (-5) 2) (x (-5) 13)
                        have b20188 := hb (x (-5) 2)
                        have b20189 := hb (x (-5) 2 && x (-5) 13)
                        clear * - r20187 b20188 b20189 d20178
                        omega
                      have d20190 : (x (-5) 10).toNat = 0 := by
                        have r20191 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
                        have b20192 := hb (x (-5) 2)
                        have b20193 := hb (x (-5) 10)
                        clear * - r20191 b20192 b20193 d20178
                        omega
                      have d20194 : (x (-6) 3).toNat = 0 := by
                        have r20195 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20196 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                        have e20197 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                        have b20198 := hb (x (-6) 3)
                        have b20199 := hb (x (-5) 2)
                        have b20200 := hb (x (-4) 13)
                        have b20201 := hb (x (-3) 12)
                        clear * - r20195 e20196 e20197 b20198 b20199 b20200 b20201 d20174 d20094 d20178
                        omega
                      have d20202 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
                        have r20203 := hand1 (x (-6) 3) (x (-6) 14)
                        have b20204 := hb (x (-6) 3)
                        have b20205 := hb (x (-6) 3 && x (-6) 14)
                        clear * - r20203 b20204 b20205 d20194
                        omega
                      have d20206 : (x (-6) 11).toNat = 0 := by
                        have r20207 : (x (-6) 11).toNat ≤ (x (-6) 3).toNat := himp _ _ (hp11 (-6))
                        have b20208 := hb (x (-6) 3)
                        have b20209 := hb (x (-6) 11)
                        clear * - r20207 b20208 b20209 d20194
                        omega
                      have d20210 : (x (-2) 11).toNat = 0 := by
                        have r20211 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
                        have b20212 := hb (x (-2) 3)
                        have b20213 := hb (x (-2) 11)
                        clear * - r20211 b20212 b20213 d20155
                        omega
                      have d20214 : (x (-2) 7 && x (-2) 11).toNat = 0 := by
                        have r20215 := hand2 (x (-2) 7) (x (-2) 11)
                        have b20216 := hb (x (-2) 11)
                        have b20217 := hb (x (-2) 7 && x (-2) 11)
                        clear * - r20215 b20216 b20217 d20210
                        omega
                      have d20218 : (x 0 7 && x 0 14).toNat = 0 := by
                        have r20219 := hand2 (x 0 7) (x 0 14)
                        have b20220 := hb (x 0 14)
                        have b20221 := hb (x 0 7 && x 0 14)
                        clear * - r20219 b20220 b20221 d20134
                        omega
                      have d20222 : (x 0 8 && x 0 14).toNat = 0 := by
                        have r20223 := hand2 (x 0 8) (x 0 14)
                        have b20224 := hb (x 0 14)
                        have b20225 := hb (x 0 8 && x 0 14)
                        clear * - r20223 b20224 b20225 d20134
                        omega
                      have d20226 : (x (-7) 4).toNat = 1 := by
                        have r20227 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := by have q := hcov11 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20228 := hb (x (-7) 4)
                        have b20229 := hb (x (-3) 11)
                        have b20230 := hb (x (-4) 1 && x (-4) 12)
                        have b20231 := hb (x (-5) 2 && x (-5) 13)
                        have b20232 := hb (x (-6) 3 && x (-6) 14)
                        clear * - r20227 b20228 b20229 b20230 b20231 b20232 d19285 d20090 d20186 d20202
                        omega
                      have d20233 : (x (-7) 12).toNat = 1 := by
                        have r20234 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
                        have b20235 := hb (x (-7) 4)
                        have b20236 := hb (x (-7) 12)
                        clear * - r20234 b20235 b20236 d20226
                        omega
                      have d20237 : (x (-8) 13).toNat = 0 := by
                        have r20238 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20239 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                        have e20240 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                        have b20241 := hb (x (-10) 3)
                        have b20242 := hb (x (-9) 2)
                        have b20243 := hb (x (-8) 13)
                        have b20244 := hb (x (-7) 12)
                        clear * - r20238 e20239 e20240 b20241 b20242 b20243 b20244 d20233
                        omega
                      have d20245 : (x (-8) 5).toNat = 0 := by
                        have r20246 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
                        have b20247 := hb (x (-8) 5)
                        have b20248 := hb (x (-8) 13)
                        clear * - r20246 b20247 b20248 d20237
                        omega
                      have d20249 : (x (-3) 8).toNat = 0 := by
                        have r20250 : (x (-3) 8).toNat + (x (-4) 1 && x (-4) 9).toNat + (x (-5) 2 && x (-5) 10).toNat + (x (-6) 3 && x (-6) 11).toNat + (x (-7) 4 && x (-7) 12).toNat + (x (-8) 5 && x (-8) 13).toNat + (x (-9) 6 && x (-9) 14).toNat + (x (-10) 7).toNat = 1 := by have q := hd8 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20251 : (x (-4) 1 && x (-4) 9).toNat = (x (-4) 9).toNat := handr _ _ (fun h => hp9 (-4) (h))
                        have e20252 : (x (-5) 2 && x (-5) 10).toNat = (x (-5) 10).toNat := handr _ _ (fun h => hp10 (-5) (h))
                        have e20253 : (x (-6) 3 && x (-6) 11).toNat = (x (-6) 11).toNat := handr _ _ (fun h => hp11 (-6) (h))
                        have e20254 : (x (-7) 4 && x (-7) 12).toNat = (x (-7) 4).toNat := handl _ _ (fun h => hp4 (-7) (h))
                        have e20255 : (x (-8) 5 && x (-8) 13).toNat = (x (-8) 5).toNat := handl _ _ (fun h => hp5 (-8) (h))
                        have e20256 : (x (-9) 6 && x (-9) 14).toNat = (x (-9) 6).toNat := handl _ _ (fun h => hp6 (-9) (h))
                        have b20257 := hb (x (-10) 7)
                        have b20258 := hb (x (-9) 6)
                        have b20259 := hb (x (-8) 5)
                        have b20260 := hb (x (-7) 4)
                        have b20261 := hb (x (-6) 11)
                        have b20262 := hb (x (-5) 10)
                        have b20263 := hb (x (-4) 9)
                        have b20264 := hb (x (-3) 8)
                        clear * - r20250 e20251 e20252 e20253 e20254 e20255 e20256 b20257 b20258 b20259 b20260 b20261 b20262 b20263 b20264 d20102 d20190 d20206 d20226 d20245
                        omega
                      have d20265 : (x (-3) 8 && x (-3) 12).toNat = 0 := by
                        have r20266 := hand1 (x (-3) 8) (x (-3) 12)
                        have b20267 := hb (x (-3) 8)
                        have b20268 := hb (x (-3) 8 && x (-3) 12)
                        clear * - r20266 b20267 b20268 d20249
                        omega
                      have d20269 : (x 7 7).toNat = 1 := by
                        have r20270 : 1 ≤ (x 7 7).toNat + (x 6 1 && x 6 8).toNat + (x 5 2 && x 5 9).toNat + (x 4 3 && x 4 10).toNat + (x 3 4 && x 3 11).toNat + (x 2 5 && x 2 12).toNat + (x 1 6 && x 1 13).toNat + (x 0 7 && x 0 14).toNat + (x (-1) 8).toNat := by have q := hcov7 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20271 := hb (x (-1) 8)
                        have b20272 := hb (x 7 7)
                        have b20273 := hb (x 6 1 && x 6 8)
                        have b20274 := hb (x 5 2 && x 5 9)
                        have b20275 := hb (x 4 3 && x 4 10)
                        have b20276 := hb (x 3 4 && x 3 11)
                        have b20277 := hb (x 2 5 && x 2 12)
                        have b20278 := hb (x 1 6 && x 1 13)
                        have b20279 := hb (x 0 7 && x 0 14)
                        clear * - r20270 b20271 b20272 b20273 b20274 b20275 b20276 b20277 b20278 b20279 d19658 d19682 d19706 g15 g16 g17 d20218 f19769
                        omega
                      have d20280 : (x 14 8).toNat = 0 := by
                        have r20281 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20282 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                        have e20283 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                        have e20284 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                        have e20285 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                        have e20286 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                        have e20287 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                        have b20288 := hb (x 7 7)
                        have b20289 := hb (x 8 6)
                        have b20290 := hb (x 9 5)
                        have b20291 := hb (x 10 4)
                        have b20292 := hb (x 11 11)
                        have b20293 := hb (x 12 10)
                        have b20294 := hb (x 13 9)
                        have b20295 := hb (x 14 8)
                        clear * - r20281 e20282 e20283 e20284 e20285 e20286 e20287 b20288 b20289 b20290 b20291 b20292 b20293 b20294 b20295 d20269
                        omega
                      have d20296 : (x 13 9).toNat = 0 := by
                        have r20297 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20298 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                        have e20299 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                        have e20300 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                        have e20301 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                        have e20302 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                        have e20303 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                        have b20304 := hb (x 7 7)
                        have b20305 := hb (x 8 6)
                        have b20306 := hb (x 9 5)
                        have b20307 := hb (x 10 4)
                        have b20308 := hb (x 11 11)
                        have b20309 := hb (x 12 10)
                        have b20310 := hb (x 13 9)
                        have b20311 := hb (x 14 8)
                        clear * - r20297 e20298 e20299 e20300 e20301 e20302 e20303 b20304 b20305 b20306 b20307 b20308 b20309 b20310 b20311 d20280 d20269
                        omega
                      have d20312 : (x 12 10).toNat = 0 := by
                        have r20313 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20314 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                        have e20315 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                        have e20316 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                        have e20317 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                        have e20318 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                        have e20319 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                        have b20320 := hb (x 7 7)
                        have b20321 := hb (x 8 6)
                        have b20322 := hb (x 9 5)
                        have b20323 := hb (x 10 4)
                        have b20324 := hb (x 11 11)
                        have b20325 := hb (x 12 10)
                        have b20326 := hb (x 13 9)
                        have b20327 := hb (x 14 8)
                        clear * - r20313 e20314 e20315 e20316 e20317 e20318 e20319 b20320 b20321 b20322 b20323 b20324 b20325 b20326 b20327 d20280 d20296 d20269
                        omega
                      have d20328 : (x 12 1 && x 12 10).toNat = 0 := by
                        have r20329 := hand2 (x 12 1) (x 12 10)
                        have b20330 := hb (x 12 10)
                        have b20331 := hb (x 12 1 && x 12 10)
                        clear * - r20329 b20330 b20331 d20312
                        omega
                      have d20332 : (x 11 11).toNat = 0 := by
                        have r20333 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20334 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                        have e20335 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                        have e20336 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                        have e20337 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                        have e20338 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                        have e20339 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                        have b20340 := hb (x 7 7)
                        have b20341 := hb (x 8 6)
                        have b20342 := hb (x 9 5)
                        have b20343 := hb (x 10 4)
                        have b20344 := hb (x 11 11)
                        have b20345 := hb (x 12 10)
                        have b20346 := hb (x 13 9)
                        have b20347 := hb (x 14 8)
                        clear * - r20333 e20334 e20335 e20336 e20337 e20338 e20339 b20340 b20341 b20342 b20343 b20344 b20345 b20346 b20347 d20280 d20296 d20312 d20269
                        omega
                      have d20348 : (x 11 2 && x 11 11).toNat = 0 := by
                        have r20349 := hand2 (x 11 2) (x 11 11)
                        have b20350 := hb (x 11 11)
                        have b20351 := hb (x 11 2 && x 11 11)
                        clear * - r20349 b20350 b20351 d20332
                        omega
                      have d20352 : (x 10 4).toNat = 0 := by
                        have r20353 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20354 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                        have e20355 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                        have e20356 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                        have e20357 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                        have e20358 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                        have e20359 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                        have b20360 := hb (x 7 7)
                        have b20361 := hb (x 8 6)
                        have b20362 := hb (x 9 5)
                        have b20363 := hb (x 10 4)
                        have b20364 := hb (x 11 11)
                        have b20365 := hb (x 12 10)
                        have b20366 := hb (x 13 9)
                        have b20367 := hb (x 14 8)
                        clear * - r20353 e20354 e20355 e20356 e20357 e20358 e20359 b20360 b20361 b20362 b20363 b20364 b20365 b20366 b20367 d20280 d20296 d20312 d20332 d20269
                        omega
                      have d20368 : (x 9 5).toNat = 0 := by
                        have r20369 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20370 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                        have e20371 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                        have e20372 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                        have e20373 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                        have e20374 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                        have e20375 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                        have b20376 := hb (x 7 7)
                        have b20377 := hb (x 8 6)
                        have b20378 := hb (x 9 5)
                        have b20379 := hb (x 10 4)
                        have b20380 := hb (x 11 11)
                        have b20381 := hb (x 12 10)
                        have b20382 := hb (x 13 9)
                        have b20383 := hb (x 14 8)
                        clear * - r20369 e20370 e20371 e20372 e20373 e20374 e20375 b20376 b20377 b20378 b20379 b20380 b20381 b20382 b20383 d20280 d20296 d20312 d20332 d20352 d20269
                        omega
                      have d20384 : (x 8 6).toNat = 0 := by
                        have r20385 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20386 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
                        have e20387 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
                        have e20388 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
                        have e20389 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
                        have e20390 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
                        have e20391 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
                        have b20392 := hb (x 7 7)
                        have b20393 := hb (x 8 6)
                        have b20394 := hb (x 9 5)
                        have b20395 := hb (x 10 4)
                        have b20396 := hb (x 11 11)
                        have b20397 := hb (x 12 10)
                        have b20398 := hb (x 13 9)
                        have b20399 := hb (x 14 8)
                        clear * - r20385 e20386 e20387 e20388 e20389 e20390 e20391 b20392 b20393 b20394 b20395 b20396 b20397 b20398 b20399 d20280 d20296 d20312 d20332 d20352 d20368 d20269
                        omega
                      have d20400 : (x 2 3 && x 2 7).toNat = 1 := by
                        have r20401 : 1 ≤ (x 5 4).toNat + (x 4 1 && x 4 5).toNat + (x 3 2 && x 3 6).toNat + (x 2 3 && x 2 7).toNat + (x 1 4 && x 1 8).toNat + (x 0 5 && x 0 9).toNat + (x (-1) 6 && x (-1) 10).toNat + (x (-2) 7 && x (-2) 11).toNat + (x (-3) 8 && x (-3) 12).toNat + (x (-4) 9 && x (-4) 13).toNat + (x (-5) 10 && x (-5) 14).toNat + (x (-6) 11).toNat := by have q := hcov4 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20402 : (x 4 1 && x 4 5).toNat = (x 4 5).toNat := handr _ _ (fun h => hp13 4 (hp5 4 (h)))
                        have e20403 : (x (-5) 10 && x (-5) 14).toNat = (x (-5) 10).toNat := handl _ _ (fun h => hp2 (-5) (hp10 (-5) (h)))
                        have b20404 := hb (x (-6) 11)
                        have b20405 := hb (x (-5) 10)
                        have b20406 := hb (x 4 5)
                        have b20407 := hb (x 5 4)
                        have b20408 := hb (x 3 2 && x 3 6)
                        have b20409 := hb (x 2 3 && x 2 7)
                        have b20410 := hb (x 1 4 && x 1 8)
                        have b20411 := hb (x 0 5 && x 0 9)
                        have b20412 := hb (x (-1) 6 && x (-1) 10)
                        have b20413 := hb (x (-2) 7 && x (-2) 11)
                        have b20414 := hb (x (-3) 8 && x (-3) 12)
                        have b20415 := hb (x (-4) 9 && x (-4) 13)
                        clear * - r20401 e20402 e20403 b20404 b20405 b20406 b20407 b20408 b20409 b20410 b20411 b20412 b20413 b20414 b20415 d19516 d19532 d19440 d19756 g12 d19762 d20214 d20265 d20098 d20190 d20206
                        omega
                      have d20416 : (x 2 7).toNat = 1 := by
                        have r20417 := hand2 (x 2 3) (x 2 7)
                        have b20418 := hb (x 2 7)
                        have b20419 := hb (x 2 3 && x 2 7)
                        clear * - r20417 b20418 b20419 d20400
                        omega
                      have d20420 : (x 9 8).toNat = 0 := by
                        have r20421 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20422 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                        have e20423 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                        have e20424 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                        have e20425 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                        have e20426 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                        have e20427 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                        have b20428 := hb (x 2 7)
                        have b20429 := hb (x 3 6)
                        have b20430 := hb (x 4 5)
                        have b20431 := hb (x 5 4)
                        have b20432 := hb (x 6 11)
                        have b20433 := hb (x 7 10)
                        have b20434 := hb (x 8 9)
                        have b20435 := hb (x 9 8)
                        clear * - r20421 e20422 e20423 e20424 e20425 e20426 e20427 b20428 b20429 b20430 b20431 b20432 b20433 b20434 b20435 d19516 d19532 d19436 d20416
                        omega
                      have d20436 : (x 8 9).toNat = 0 := by
                        have r20437 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20438 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                        have e20439 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                        have e20440 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                        have e20441 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                        have e20442 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                        have e20443 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                        have b20444 := hb (x 2 7)
                        have b20445 := hb (x 3 6)
                        have b20446 := hb (x 4 5)
                        have b20447 := hb (x 5 4)
                        have b20448 := hb (x 6 11)
                        have b20449 := hb (x 7 10)
                        have b20450 := hb (x 8 9)
                        have b20451 := hb (x 9 8)
                        clear * - r20437 e20438 e20439 e20440 e20441 e20442 e20443 b20444 b20445 b20446 b20447 b20448 b20449 b20450 b20451 d20420 d19516 d19532 d19436 d20416
                        omega
                      have d20452 : (x 7 10).toNat = 0 := by
                        have r20453 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20454 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
                        have e20455 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
                        have e20456 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
                        have e20457 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
                        have e20458 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
                        have e20459 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
                        have b20460 := hb (x 2 7)
                        have b20461 := hb (x 3 6)
                        have b20462 := hb (x 4 5)
                        have b20463 := hb (x 5 4)
                        have b20464 := hb (x 6 11)
                        have b20465 := hb (x 7 10)
                        have b20466 := hb (x 8 9)
                        have b20467 := hb (x 9 8)
                        clear * - r20453 e20454 e20455 e20456 e20457 e20458 e20459 b20460 b20461 b20462 b20463 b20464 b20465 b20466 b20467 d20420 d20436 d19516 d19532 d19436 d20416
                        omega
                      have d20468 : (x 6 1 && x 6 11).toNat = 1 := by
                        have r20469 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20470 := hb (x 2 5)
                        have b20471 := hb (x 7 10)
                        have b20472 := hb (x 6 1 && x 6 11)
                        have b20473 := hb (x 5 2 && x 5 12)
                        have b20474 := hb (x 4 3 && x 4 13)
                        have b20475 := hb (x 3 4 && x 3 14)
                        clear * - r20469 b20470 b20471 b20472 b20473 b20474 b20475 d20452 d19512 d19528 g28 g7
                        omega
                      have d20476 : (x 6 11).toNat = 1 := by
                        have r20477 := hand2 (x 6 1) (x 6 11)
                        have b20478 := hb (x 6 11)
                        have b20479 := hb (x 6 1 && x 6 11)
                        clear * - r20477 b20478 b20479 d20468
                        omega
                      have d20480 : (x 6 3).toNat = 1 := by
                        have r20481 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
                        have b20482 := hb (x 6 3)
                        have b20483 := hb (x 6 11)
                        clear * - r20481 b20482 b20483 d20476
                        omega
                      have d20484 : (x 9 12).toNat = 0 := by
                        have r20485 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20486 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                        have e20487 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                        have b20488 := hb (x 6 3)
                        have b20489 := hb (x 7 2)
                        have b20490 := hb (x 8 13)
                        have b20491 := hb (x 9 12)
                        clear * - r20485 e20486 e20487 b20488 b20489 b20490 b20491 d20480
                        omega
                      have d20492 : (x 9 4).toNat = 0 := by
                        have r20493 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
                        have b20494 := hb (x 9 4)
                        have b20495 := hb (x 9 12)
                        clear * - r20493 b20494 b20495 d20484
                        omega
                      have d20496 : (x 9 4 && x 9 13).toNat = 0 := by
                        have r20497 := hand1 (x 9 4) (x 9 13)
                        have b20498 := hb (x 9 4)
                        have b20499 := hb (x 9 4 && x 9 13)
                        clear * - r20497 b20498 b20499 d20492
                        omega
                      have d20500 : (x 8 13).toNat = 0 := by
                        have r20501 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20502 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                        have e20503 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                        have b20504 := hb (x 6 3)
                        have b20505 := hb (x 7 2)
                        have b20506 := hb (x 8 13)
                        have b20507 := hb (x 9 12)
                        clear * - r20501 e20502 e20503 b20504 b20505 b20506 b20507 d20484 d20480
                        omega
                      have d20508 : (x 8 5).toNat = 0 := by
                        have r20509 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
                        have b20510 := hb (x 8 5)
                        have b20511 := hb (x 8 13)
                        clear * - r20509 b20510 b20511 d20500
                        omega
                      have d20512 : (x 8 5 && x 8 14).toNat = 0 := by
                        have r20513 := hand1 (x 8 5) (x 8 14)
                        have b20514 := hb (x 8 5)
                        have b20515 := hb (x 8 5 && x 8 14)
                        clear * - r20513 b20514 b20515 d20508
                        omega
                      have d20516 : (x 7 2).toNat = 0 := by
                        have r20517 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20518 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
                        have e20519 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
                        have b20520 := hb (x 6 3)
                        have b20521 := hb (x 7 2)
                        have b20522 := hb (x 8 13)
                        have b20523 := hb (x 9 12)
                        clear * - r20517 e20518 e20519 b20520 b20521 b20522 b20523 d20484 d20500 d20480
                        omega
                      have d20524 : (x 6 1).toNat = 1 := by
                        have r20525 := hand1 (x 6 1) (x 6 11)
                        have b20526 := hb (x 6 1)
                        have b20527 := hb (x 6 1 && x 6 11)
                        clear * - r20525 b20526 b20527 d20468
                        omega
                      have d20528 : (x 7 14).toNat = 0 := by
                        have r20529 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20530 := hb (x 6 1)
                        have b20531 := hb (x 7 14)
                        clear * - r20529 b20530 b20531 d20524
                        omega
                      have d20532 : (x 7 1 && x 7 14).toNat = 0 := by
                        have r20533 := hand2 (x 7 1) (x 7 14)
                        have b20534 := hb (x 7 14)
                        have b20535 := hb (x 7 1 && x 7 14)
                        clear * - r20533 b20534 b20535 d20528
                        omega
                      have d20536 : (x 6 2).toNat = 1 := by
                        have r20537 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20538 := hb (x 6 2)
                        have b20539 := hb (x 8 13)
                        have b20540 := hb (x 7 1 && x 7 14)
                        clear * - r20537 b20538 b20539 b20540 d20500 d20532
                        omega
                      have d20541 : (x 6 14).toNat = 1 := by
                        have r20542 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
                        have b20543 := hb (x 6 2)
                        have b20544 := hb (x 6 14)
                        clear * - r20542 b20543 b20544 d20536
                        omega
                      have d20545 : (x 5 1).toNat = 0 := by
                        have r20546 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20547 := hb (x 5 1)
                        have b20548 := hb (x 6 14)
                        clear * - r20546 b20547 b20548 d20541
                        omega
                      have d20549 : (x 5 13).toNat = 0 := by
                        have r20550 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
                        have b20551 := hb (x 5 1)
                        have b20552 := hb (x 5 13)
                        clear * - r20550 b20551 b20552 d20545
                        omega
                      have d20553 : (x 4 1 && x 4 14).toNat = 1 := by
                        have r20554 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20555 := hb (x 3 2)
                        have b20556 := hb (x 5 13)
                        have b20557 := hb (x 4 1 && x 4 14)
                        clear * - r20554 b20555 b20556 b20557 d20549 d19444
                        omega
                      have d20558 : (x 4 1).toNat = 1 := by
                        have r20559 := hand1 (x 4 1) (x 4 14)
                        have b20560 := hb (x 4 1)
                        have b20561 := hb (x 4 1 && x 4 14)
                        clear * - r20559 b20560 b20561 d20553
                        omega
                      have d20562 : (x 5 14).toNat = 0 := by
                        have r20563 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20564 := hb (x 4 1)
                        have b20565 := hb (x 5 14)
                        clear * - r20563 b20564 b20565 d20558
                        omega
                      have d20566 : (x 5 2).toNat = 0 := by
                        have r20567 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
                        have b20568 := hb (x 5 2)
                        have b20569 := hb (x 5 14)
                        clear * - r20567 b20568 b20569 d20562
                        omega
                      have d20570 : (x 5 2 && x 5 11).toNat = 0 := by
                        have r20571 := hand1 (x 5 2) (x 5 11)
                        have b20572 := hb (x 5 2)
                        have b20573 := hb (x 5 2 && x 5 11)
                        clear * - r20571 b20572 b20573 d20566
                        omega
                      have d20574 : (x 8 12).toNat = 0 := by
                        have r20575 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20576 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                        have e20577 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                        have b20578 := hb (x 5 3)
                        have b20579 := hb (x 6 2)
                        have b20580 := hb (x 7 13)
                        have b20581 := hb (x 8 12)
                        clear * - r20575 e20576 e20577 b20578 b20579 b20580 b20581 d20536
                        omega
                      have d20582 : (x 7 13).toNat = 0 := by
                        have r20583 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20584 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                        have e20585 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                        have b20586 := hb (x 5 3)
                        have b20587 := hb (x 6 2)
                        have b20588 := hb (x 7 13)
                        have b20589 := hb (x 8 12)
                        clear * - r20583 e20584 e20585 b20586 b20587 b20588 b20589 d20574 d20536
                        omega
                      have d20590 : (x 5 3).toNat = 0 := by
                        have r20591 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20592 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
                        have e20593 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
                        have b20594 := hb (x 5 3)
                        have b20595 := hb (x 6 2)
                        have b20596 := hb (x 7 13)
                        have b20597 := hb (x 8 12)
                        clear * - r20591 e20592 e20593 b20594 b20595 b20596 b20597 d20574 d20582 d20536
                        omega
                      have d20598 : (x 5 11).toNat = 0 := by
                        have r20599 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
                        have b20600 := hb (x 5 3)
                        have b20601 := hb (x 5 11)
                        clear * - r20599 b20600 b20601 d20590
                        omega
                      have d20602 : (x 7 6).toNat = 0 := by
                        have r20603 : (x 7 6).toNat ≤ (x 7 14).toNat := himp _ _ (hp6 7)
                        have b20604 := hb (x 7 6)
                        have b20605 := hb (x 7 14)
                        clear * - r20603 b20604 b20605 d20528
                        omega
                      have d20606 : (x 10 3 && x 10 12).toNat = 1 := by
                        have r20607 : 1 ≤ (x 13 9).toNat + (x 12 1 && x 12 10).toNat + (x 11 2 && x 11 11).toNat + (x 10 3 && x 10 12).toNat + (x 9 4 && x 9 13).toNat + (x 8 5 && x 8 14).toNat + (x 7 6).toNat := by have q := hcov9 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20608 := hb (x 7 6)
                        have b20609 := hb (x 13 9)
                        have b20610 := hb (x 12 1 && x 12 10)
                        have b20611 := hb (x 11 2 && x 11 11)
                        have b20612 := hb (x 10 3 && x 10 12)
                        have b20613 := hb (x 9 4 && x 9 13)
                        have b20614 := hb (x 8 5 && x 8 14)
                        clear * - r20607 b20608 b20609 b20610 b20611 b20612 b20613 b20614 d20296 d20328 d20348 d20496 d20512 d20602
                        omega
                      have d20615 : (x 10 12).toNat = 1 := by
                        have r20616 := hand2 (x 10 3) (x 10 12)
                        have b20617 := hb (x 10 12)
                        have b20618 := hb (x 10 3 && x 10 12)
                        clear * - r20616 b20617 b20618 d20606
                        omega
                      have d20619 : (x 9 13).toNat = 0 := by
                        have r20620 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20621 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                        have e20622 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                        have b20623 := hb (x 7 3)
                        have b20624 := hb (x 8 2)
                        have b20625 := hb (x 9 13)
                        have b20626 := hb (x 10 12)
                        clear * - r20620 e20621 e20622 b20623 b20624 b20625 b20626 d20615
                        omega
                      have d20627 : (x 8 1 && x 8 14).toNat = 1 := by
                        have r20628 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20629 := hb (x 7 2)
                        have b20630 := hb (x 9 13)
                        have b20631 := hb (x 8 1 && x 8 14)
                        clear * - r20628 b20629 b20630 b20631 d20619 d20516
                        omega
                      have d20632 : (x 8 14).toNat = 1 := by
                        have r20633 := hand2 (x 8 1) (x 8 14)
                        have b20634 := hb (x 8 14)
                        have b20635 := hb (x 8 1 && x 8 14)
                        clear * - r20633 b20634 b20635 d20627
                        omega
                      have d20636 : (x 7 1).toNat = 0 := by
                        have r20637 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20638 := hb (x 7 1)
                        have b20639 := hb (x 8 14)
                        clear * - r20637 b20638 b20639 d20632
                        omega
                      have d20640 : (x 7 1 && x 7 7).toNat = 0 := by
                        have r20641 := hand1 (x 7 1) (x 7 7)
                        have b20642 := hb (x 7 1)
                        have b20643 := hb (x 7 1 && x 7 7)
                        clear * - r20641 b20642 b20643 d20636
                        omega
                      have d20644 : (x 2 6 && x 2 12).toNat = 1 := by
                        have r20645 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20646 := hb (x (-1) 9)
                        have b20647 := hb (x 8 6)
                        have b20648 := hb (x 7 1 && x 7 7)
                        have b20649 := hb (x 6 2 && x 6 8)
                        have b20650 := hb (x 5 3 && x 5 9)
                        have b20651 := hb (x 4 4 && x 4 10)
                        have b20652 := hb (x 3 5 && x 3 11)
                        have b20653 := hb (x 2 6 && x 2 12)
                        have b20654 := hb (x 1 7 && x 1 13)
                        have b20655 := hb (x 0 8 && x 0 14)
                        clear * - r20645 b20646 b20647 b20648 b20649 b20650 b20651 b20652 b20653 b20654 b20655 d20384 d20640 d19662 d19686 d19577 d19593 d19553 d20222 d19241
                        omega
                      have d20656 : (x 2 6).toNat = 1 := by
                        have r20657 := hand1 (x 2 6) (x 2 12)
                        have b20658 := hb (x 2 6)
                        have b20659 := hb (x 2 6 && x 2 12)
                        clear * - r20657 b20658 b20659 d20644
                        omega
                      have d20660 : (x 8 8).toNat = 0 := by
                        have r20661 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20662 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e20663 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e20664 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e20665 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e20666 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e20667 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have b20668 := hb (x 1 7)
                        have b20669 := hb (x 2 6)
                        have b20670 := hb (x 3 5)
                        have b20671 := hb (x 4 4)
                        have b20672 := hb (x 5 11)
                        have b20673 := hb (x 6 10)
                        have b20674 := hb (x 7 9)
                        have b20675 := hb (x 8 8)
                        clear * - r20661 e20662 e20663 e20664 e20665 e20666 e20667 b20668 b20669 b20670 b20671 b20672 b20673 b20674 b20675 d20598 d19573 d19589 d20656 f19767
                        omega
                      have d20676 : (x 7 9).toNat = 0 := by
                        have r20677 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have e20678 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                        have e20679 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                        have e20680 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                        have e20681 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                        have e20682 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                        have e20683 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                        have b20684 := hb (x 1 7)
                        have b20685 := hb (x 2 6)
                        have b20686 := hb (x 3 5)
                        have b20687 := hb (x 4 4)
                        have b20688 := hb (x 5 11)
                        have b20689 := hb (x 6 10)
                        have b20690 := hb (x 7 9)
                        have b20691 := hb (x 8 8)
                        clear * - r20677 e20678 e20679 e20680 e20681 e20682 e20683 b20684 b20685 b20686 b20687 b20688 b20689 b20690 b20691 d20660 d20598 d19573 d19589 d20656 f19767
                        omega
                      have d20692 : (x 6 1 && x 6 10).toNat = 1 := by
                        have r20693 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                        have b20694 := hb (x 1 6)
                        have b20695 := hb (x 7 9)
                        have b20696 := hb (x 6 1 && x 6 10)
                        have b20697 := hb (x 5 2 && x 5 11)
                        have b20698 := hb (x 4 3 && x 4 12)
                        have b20699 := hb (x 3 4 && x 3 13)
                        have b20700 := hb (x 2 5 && x 2 14)
                        clear * - r20693 b20694 b20695 b20696 b20697 b20698 b20699 b20700 d20676 d20570 d19569 g22 g23 g5
                        omega
                      have d20701 : (x 6 10).toNat = 1 := by
                        have r20702 := hand2 (x 6 1) (x 6 10)
                        have b20703 := hb (x 6 10)
                        have b20704 := hb (x 6 1 && x 6 10)
                        clear * - r20702 b20703 b20704 d20692
                        omega
                      have r20705 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e20706 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                      have e20707 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                      have e20708 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                      have e20709 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                      have e20710 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                      have e20711 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                      have b20712 := hb (x 1 7)
                      have b20713 := hb (x 2 6)
                      have b20714 := hb (x 3 5)
                      have b20715 := hb (x 4 4)
                      have b20716 := hb (x 5 11)
                      have b20717 := hb (x 6 10)
                      have b20718 := hb (x 7 9)
                      have b20719 := hb (x 8 8)
                      linarith only [r20705, e20706, e20707, e20708, e20709, e20710, e20711, b20712, b20713, b20714, b20715, b20716, b20717, b20718, b20719, d20660, d20676, d20701, d20598, d19573, d19589, d20656, f19767]
                  · have f20720 : (x (-1) 13).toNat = 1 := by rw [h19784]; rfl
                    have d20721 : (x (-1) 1).toNat = 1 := by
                      have r20722 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
                      have b20723 := hb (x (-1) 1)
                      have b20724 := hb (x (-1) 13)
                      clear * - r20722 b20723 b20724 f20720
                      omega
                    have d20725 : (x 0 14).toNat = 0 := by
                      have r20726 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b20727 := hb (x (-1) 1)
                      have b20728 := hb (x 0 14)
                      clear * - r20726 b20727 b20728 d20721
                      omega
                    have d20729 : (x 0 1 && x 0 14).toNat = 0 := by
                      have r20730 := hand2 (x 0 1) (x 0 14)
                      have b20731 := hb (x 0 14)
                      have b20732 := hb (x 0 1 && x 0 14)
                      clear * - r20730 b20731 b20732 d20725
                      omega
                    have d20733 : (x (-1) 2).toNat = 1 := by
                      have r20734 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b20735 := hb (x (-1) 2)
                      have b20736 := hb (x 1 13)
                      have b20737 := hb (x 0 1 && x 0 14)
                      clear * - r20734 b20735 b20736 b20737 d19549 d20729
                      omega
                    have d20738 : (x (-1) 14).toNat = 1 := by
                      have r20739 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
                      have b20740 := hb (x (-1) 2)
                      have b20741 := hb (x (-1) 14)
                      clear * - r20739 b20740 b20741 d20733
                      omega
                    have d20742 : (x (-2) 1).toNat = 0 := by
                      have r20743 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have b20744 := hb (x (-2) 1)
                      have b20745 := hb (x (-1) 14)
                      clear * - r20743 b20744 b20745 d20738
                      omega
                    have d20746 : (x (-2) 13).toNat = 0 := by
                      have r20747 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                      have b20748 := hb (x (-2) 1)
                      have b20749 := hb (x (-2) 13)
                      clear * - r20747 b20748 b20749 d20742
                      omega
                    have d20750 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
                      have r20751 := hand2 (x (-2) 2) (x (-2) 13)
                      have b20752 := hb (x (-2) 13)
                      have b20753 := hb (x (-2) 2 && x (-2) 13)
                      clear * - r20751 b20752 b20753 d20746
                      omega
                    have d20754 : (x (-2) 2).toNat = 0 := by
                      have r20755 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e20756 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                      have e20757 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                      have b20758 := hb (x (-3) 3)
                      have b20759 := hb (x (-2) 2)
                      have b20760 := hb (x (-1) 13)
                      have b20761 := hb (x 0 12)
                      clear * - r20755 e20756 e20757 b20758 b20759 b20760 b20761 f19749 f20720
                      omega
                    have d20762 : (x (-3) 3).toNat = 0 := by
                      have r20763 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                      have e20764 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                      have e20765 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                      have b20766 := hb (x (-3) 3)
                      have b20767 := hb (x (-2) 2)
                      have b20768 := hb (x (-1) 13)
                      have b20769 := hb (x 0 12)
                      clear * - r20763 e20764 e20765 b20766 b20767 b20768 b20769 f19749 f20720 d20754
                      omega
                    have d20770 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
                      have r20771 := hand1 (x (-3) 3) (x (-3) 14)
                      have b20772 := hb (x (-3) 3)
                      have b20773 := hb (x (-3) 3 && x (-3) 14)
                      clear * - r20771 b20772 b20773 d20762
                      omega
                    have r20774 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have b20775 := hb (x (-4) 4)
                    have b20776 := hb (x 0 11)
                    have b20777 := hb (x (-1) 1 && x (-1) 12)
                    have b20778 := hb (x (-2) 2 && x (-2) 13)
                    have b20779 := hb (x (-3) 3 && x (-3) 14)
                    linarith only [r20774, b20775, b20776, b20777, b20778, b20779, d19484, d19772, d20750, d20770, d19313]
                · have f20780 : (x (-1) 12).toNat = 1 := by rw [h19770]; rfl
                  have d20781 : (x (-2) 13).toNat = 0 := by
                    have r20782 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e20783 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                    have e20784 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                    have b20785 := hb (x (-4) 3)
                    have b20786 := hb (x (-3) 2)
                    have b20787 := hb (x (-2) 13)
                    have b20788 := hb (x (-1) 12)
                    clear * - r20782 e20783 e20784 b20785 b20786 b20787 b20788 f20780
                    omega
                  have d20789 : (x (-3) 2).toNat = 0 := by
                    have r20790 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                    have e20791 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                    have e20792 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                    have b20793 := hb (x (-4) 3)
                    have b20794 := hb (x (-3) 2)
                    have b20795 := hb (x (-2) 13)
                    have b20796 := hb (x (-1) 12)
                    clear * - r20790 e20791 e20792 b20793 b20794 b20795 b20796 f20780 d20781
                    omega
                  have r20797 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20798 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                  have e20799 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                  have r20800 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20801 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                  have e20802 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                  have r20803 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r20804 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r20805 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r20806 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have r20807 := hand1 (x (-2) 2) (x (-2) 12)
                  have r20808 := hand2 (x (-2) 2) (x (-2) 12)
                  have r20809 := hand1 (x (-3) 3) (x (-3) 13)
                  have r20810 := hand2 (x (-3) 3) (x (-3) 13)
                  have r20811 := hand1 (x (-3) 1) (x (-3) 14)
                  have r20812 := hand2 (x (-2) 1) (x (-2) 14)
                  linarith only [r20797, e20798, e20799, r20800, e20801, e20802, r20803, r20804, r20805, r20806, r20807, r20808, r20809, r20810, r20811, r20812, d19341, d20789, d20781, d19415, f19749, d19638, d19329]
              · have f20833 : (x (-1) 8).toNat = 1 := by rw [h19768]; rfl
                have d20834 : (x (-2) 9).toNat = 0 := by
                  have r20835 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20836 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e20837 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e20838 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e20839 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e20840 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e20841 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b20842 := hb (x (-8) 7)
                  have b20843 := hb (x (-7) 6)
                  have b20844 := hb (x (-6) 5)
                  have b20845 := hb (x (-5) 4)
                  have b20846 := hb (x (-4) 11)
                  have b20847 := hb (x (-3) 10)
                  have b20848 := hb (x (-2) 9)
                  have b20849 := hb (x (-1) 8)
                  clear * - r20835 e20836 e20837 e20838 e20839 e20840 e20841 b20842 b20843 b20844 b20845 b20846 b20847 b20848 b20849 f20833
                  omega
                have d20850 : (x (-3) 10).toNat = 0 := by
                  have r20851 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20852 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e20853 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e20854 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e20855 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e20856 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e20857 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b20858 := hb (x (-8) 7)
                  have b20859 := hb (x (-7) 6)
                  have b20860 := hb (x (-6) 5)
                  have b20861 := hb (x (-5) 4)
                  have b20862 := hb (x (-4) 11)
                  have b20863 := hb (x (-3) 10)
                  have b20864 := hb (x (-2) 9)
                  have b20865 := hb (x (-1) 8)
                  clear * - r20851 e20852 e20853 e20854 e20855 e20856 e20857 b20858 b20859 b20860 b20861 b20862 b20863 b20864 b20865 f20833 d20834
                  omega
                have d20866 : (x (-4) 11).toNat = 0 := by
                  have r20867 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20868 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e20869 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e20870 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e20871 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e20872 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e20873 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b20874 := hb (x (-8) 7)
                  have b20875 := hb (x (-7) 6)
                  have b20876 := hb (x (-6) 5)
                  have b20877 := hb (x (-5) 4)
                  have b20878 := hb (x (-4) 11)
                  have b20879 := hb (x (-3) 10)
                  have b20880 := hb (x (-2) 9)
                  have b20881 := hb (x (-1) 8)
                  clear * - r20867 e20868 e20869 e20870 e20871 e20872 e20873 b20874 b20875 b20876 b20877 b20878 b20879 b20880 b20881 f20833 d20834 d20850
                  omega
                have d20882 : (x (-4) 1 && x (-4) 11).toNat = 0 := by
                  have r20883 := hand2 (x (-4) 1) (x (-4) 11)
                  have b20884 := hb (x (-4) 11)
                  have b20885 := hb (x (-4) 1 && x (-4) 11)
                  clear * - r20883 b20884 b20885 d20866
                  omega
                have d20886 : (x (-5) 4).toNat = 0 := by
                  have r20887 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20888 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e20889 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e20890 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e20891 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e20892 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e20893 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b20894 := hb (x (-8) 7)
                  have b20895 := hb (x (-7) 6)
                  have b20896 := hb (x (-6) 5)
                  have b20897 := hb (x (-5) 4)
                  have b20898 := hb (x (-4) 11)
                  have b20899 := hb (x (-3) 10)
                  have b20900 := hb (x (-2) 9)
                  have b20901 := hb (x (-1) 8)
                  clear * - r20887 e20888 e20889 e20890 e20891 e20892 e20893 b20894 b20895 b20896 b20897 b20898 b20899 b20900 b20901 f20833 d20834 d20850 d20866
                  omega
                have d20902 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
                  have r20903 := hand1 (x (-5) 4) (x (-5) 13)
                  have b20904 := hb (x (-5) 4)
                  have b20905 := hb (x (-5) 4 && x (-5) 13)
                  clear * - r20903 b20904 b20905 d20886
                  omega
                have d20906 : (x (-6) 5).toNat = 0 := by
                  have r20907 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20908 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e20909 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e20910 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e20911 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e20912 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e20913 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b20914 := hb (x (-8) 7)
                  have b20915 := hb (x (-7) 6)
                  have b20916 := hb (x (-6) 5)
                  have b20917 := hb (x (-5) 4)
                  have b20918 := hb (x (-4) 11)
                  have b20919 := hb (x (-3) 10)
                  have b20920 := hb (x (-2) 9)
                  have b20921 := hb (x (-1) 8)
                  clear * - r20907 e20908 e20909 e20910 e20911 e20912 e20913 b20914 b20915 b20916 b20917 b20918 b20919 b20920 b20921 f20833 d20834 d20850 d20866 d20886
                  omega
                have d20922 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
                  have r20923 := hand1 (x (-6) 5) (x (-6) 14)
                  have b20924 := hb (x (-6) 5)
                  have b20925 := hb (x (-6) 5 && x (-6) 14)
                  clear * - r20923 b20924 b20925 d20906
                  omega
                have d20926 : (x (-7) 6).toNat = 0 := by
                  have r20927 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20928 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e20929 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e20930 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e20931 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e20932 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e20933 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b20934 := hb (x (-8) 7)
                  have b20935 := hb (x (-7) 6)
                  have b20936 := hb (x (-6) 5)
                  have b20937 := hb (x (-5) 4)
                  have b20938 := hb (x (-4) 11)
                  have b20939 := hb (x (-3) 10)
                  have b20940 := hb (x (-2) 9)
                  have b20941 := hb (x (-1) 8)
                  clear * - r20927 e20928 e20929 e20930 e20931 e20932 e20933 b20934 b20935 b20936 b20937 b20938 b20939 b20940 b20941 f20833 d20834 d20850 d20866 d20886 d20906
                  omega
                have d20942 : (x (-4) 3 && x (-4) 12).toNat = 1 := by
                  have r20943 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b20944 := hb (x (-7) 6)
                  have b20945 := hb (x (-1) 9)
                  have b20946 := hb (x (-2) 1 && x (-2) 10)
                  have b20947 := hb (x (-3) 2 && x (-3) 11)
                  have b20948 := hb (x (-4) 3 && x (-4) 12)
                  have b20949 := hb (x (-5) 4 && x (-5) 13)
                  have b20950 := hb (x (-6) 5 && x (-6) 14)
                  clear * - r20943 b20944 b20945 b20946 b20947 b20948 b20949 b20950 d19241 d19277 d19305 d20902 d20922 d20926
                  omega
                have d20951 : (x (-4) 12).toNat = 1 := by
                  have r20952 := hand2 (x (-4) 3) (x (-4) 12)
                  have b20953 := hb (x (-4) 12)
                  have b20954 := hb (x (-4) 3 && x (-4) 12)
                  clear * - r20952 b20953 b20954 d20942
                  omega
                have d20955 : (x (-5) 13).toNat = 0 := by
                  have r20956 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20957 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                  have e20958 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                  have b20959 := hb (x (-7) 3)
                  have b20960 := hb (x (-6) 2)
                  have b20961 := hb (x (-5) 13)
                  have b20962 := hb (x (-4) 12)
                  clear * - r20956 e20957 e20958 b20959 b20960 b20961 b20962 d20951
                  omega
                have d20963 : (x (-6) 2).toNat = 0 := by
                  have r20964 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20965 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                  have e20966 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                  have b20967 := hb (x (-7) 3)
                  have b20968 := hb (x (-6) 2)
                  have b20969 := hb (x (-5) 13)
                  have b20970 := hb (x (-4) 12)
                  clear * - r20964 e20965 e20966 b20967 b20968 b20969 b20970 d20951 d20955
                  omega
                have d20971 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
                  have r20972 := hand1 (x (-6) 2) (x (-6) 13)
                  have b20973 := hb (x (-6) 2)
                  have b20974 := hb (x (-6) 2 && x (-6) 13)
                  clear * - r20972 b20973 b20974 d20963
                  omega
                have d20975 : (x (-7) 3).toNat = 0 := by
                  have r20976 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20977 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
                  have e20978 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
                  have b20979 := hb (x (-7) 3)
                  have b20980 := hb (x (-6) 2)
                  have b20981 := hb (x (-5) 13)
                  have b20982 := hb (x (-4) 12)
                  clear * - r20976 e20977 e20978 b20979 b20980 b20981 b20982 d20951 d20955 d20963
                  omega
                have d20983 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
                  have r20984 := hand1 (x (-7) 3) (x (-7) 14)
                  have b20985 := hb (x (-7) 3)
                  have b20986 := hb (x (-7) 3 && x (-7) 14)
                  clear * - r20984 b20985 b20986 d20975
                  omega
                have d20987 : (x (-7) 11).toNat = 0 := by
                  have r20988 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
                  have b20989 := hb (x (-7) 3)
                  have b20990 := hb (x (-7) 11)
                  clear * - r20988 b20989 b20990 d20975
                  omega
                have d20991 : (x (-4) 3).toNat = 1 := by
                  have r20992 := hand1 (x (-4) 3) (x (-4) 12)
                  have b20993 := hb (x (-4) 3)
                  have b20994 := hb (x (-4) 3 && x (-4) 12)
                  clear * - r20992 b20993 b20994 d20942
                  omega
                have d20995 : (x (-1) 12).toNat = 0 := by
                  have r20996 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e20997 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e20998 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b20999 := hb (x (-4) 3)
                  have b21000 := hb (x (-3) 2)
                  have b21001 := hb (x (-2) 13)
                  have b21002 := hb (x (-1) 12)
                  clear * - r20996 e20997 e20998 b20999 b21000 b21001 b21002 d20991
                  omega
                have d21003 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
                  have r21004 := hand2 (x (-1) 1) (x (-1) 12)
                  have b21005 := hb (x (-1) 12)
                  have b21006 := hb (x (-1) 1 && x (-1) 12)
                  clear * - r21004 b21005 b21006 d20995
                  omega
                have d21007 : (x (-2) 13).toNat = 0 := by
                  have r21008 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21009 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e21010 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b21011 := hb (x (-4) 3)
                  have b21012 := hb (x (-3) 2)
                  have b21013 := hb (x (-2) 13)
                  have b21014 := hb (x (-1) 12)
                  clear * - r21008 e21009 e21010 b21011 b21012 b21013 b21014 d20995 d20991
                  omega
                have d21015 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
                  have r21016 := hand2 (x (-2) 2) (x (-2) 13)
                  have b21017 := hb (x (-2) 13)
                  have b21018 := hb (x (-2) 2 && x (-2) 13)
                  clear * - r21016 b21017 b21018 d21007
                  omega
                have d21019 : (x (-3) 3 && x (-3) 14).toNat = 1 := by
                  have r21020 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21021 := hb (x (-4) 4)
                  have b21022 := hb (x 0 11)
                  have b21023 := hb (x (-1) 1 && x (-1) 12)
                  have b21024 := hb (x (-2) 2 && x (-2) 13)
                  have b21025 := hb (x (-3) 3 && x (-3) 14)
                  clear * - r21020 b21021 b21022 b21023 b21024 b21025 d19484 d21003 d21015 d19313
                  omega
                have d21026 : (x (-3) 14).toNat = 1 := by
                  have r21027 := hand2 (x (-3) 3) (x (-3) 14)
                  have b21028 := hb (x (-3) 14)
                  have b21029 := hb (x (-3) 3 && x (-3) 14)
                  clear * - r21027 b21028 b21029 d21019
                  omega
                have d21030 : (x (-4) 1).toNat = 0 := by
                  have r21031 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21032 := hb (x (-4) 1)
                  have b21033 := hb (x (-3) 14)
                  clear * - r21031 b21032 b21033 d21026
                  omega
                have d21034 : (x (-4) 13).toNat = 0 := by
                  have r21035 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
                  have b21036 := hb (x (-4) 1)
                  have b21037 := hb (x (-4) 13)
                  clear * - r21035 b21036 b21037 d21030
                  omega
                have d21038 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
                  have r21039 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21040 := hb (x (-6) 2)
                  have b21041 := hb (x (-4) 13)
                  have b21042 := hb (x (-5) 1 && x (-5) 14)
                  clear * - r21039 b21040 b21041 b21042 d21034 d20963
                  omega
                have d21043 : (x (-5) 14).toNat = 1 := by
                  have r21044 := hand2 (x (-5) 1) (x (-5) 14)
                  have b21045 := hb (x (-5) 14)
                  have b21046 := hb (x (-5) 1 && x (-5) 14)
                  clear * - r21044 b21045 b21046 d21038
                  omega
                have d21047 : (x (-6) 1).toNat = 0 := by
                  have r21048 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21049 := hb (x (-6) 1)
                  have b21050 := hb (x (-5) 14)
                  clear * - r21048 b21049 b21050 d21043
                  omega
                have d21051 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
                  have r21052 := hand1 (x (-6) 1) (x (-6) 14)
                  have b21053 := hb (x (-6) 1)
                  have b21054 := hb (x (-6) 1 && x (-6) 14)
                  clear * - r21052 b21053 b21054 d21047
                  omega
                have d21055 : (x (-7) 2).toNat = 1 := by
                  have r21056 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21057 := hb (x (-7) 2)
                  have b21058 := hb (x (-5) 13)
                  have b21059 := hb (x (-6) 1 && x (-6) 14)
                  clear * - r21056 b21057 b21058 b21059 d20955 d21051
                  omega
                have d21060 : (x (-7) 14).toNat = 1 := by
                  have r21061 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
                  have b21062 := hb (x (-7) 2)
                  have b21063 := hb (x (-7) 14)
                  clear * - r21061 b21062 b21063 d21055
                  omega
                have d21064 : (x (-8) 1).toNat = 0 := by
                  have r21065 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21066 := hb (x (-8) 1)
                  have b21067 := hb (x (-7) 14)
                  clear * - r21065 b21066 b21067 d21060
                  omega
                have d21068 : (x (-8) 1 && x (-8) 12).toNat = 0 := by
                  have r21069 := hand1 (x (-8) 1) (x (-8) 12)
                  have b21070 := hb (x (-8) 1)
                  have b21071 := hb (x (-8) 1 && x (-8) 12)
                  clear * - r21069 b21070 b21071 d21064
                  omega
                have d21072 : (x (-8) 13).toNat = 0 := by
                  have r21073 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
                  have b21074 := hb (x (-8) 1)
                  have b21075 := hb (x (-8) 13)
                  clear * - r21073 b21074 b21075 d21064
                  omega
                have d21076 : (x (-8) 5).toNat = 0 := by
                  have r21077 : (x (-8) 5).toNat ≤ (x (-8) 13).toNat := himp _ _ (hp5 (-8))
                  have b21078 := hb (x (-8) 5)
                  have b21079 := hb (x (-8) 13)
                  clear * - r21077 b21078 b21079 d21072
                  omega
                have d21080 : (x (-8) 9).toNat = 0 := by
                  have r21081 : (x (-8) 9).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp9 (-8))
                  have b21082 := hb (x (-8) 1)
                  have b21083 := hb (x (-8) 9)
                  clear * - r21081 b21082 b21083 d21064
                  omega
                have d21084 : (x (-5) 12).toNat = 0 := by
                  have r21085 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21086 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                  have e21087 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                  have b21088 := hb (x (-8) 3)
                  have b21089 := hb (x (-7) 2)
                  have b21090 := hb (x (-6) 13)
                  have b21091 := hb (x (-5) 12)
                  clear * - r21085 e21086 e21087 b21088 b21089 b21090 b21091 d21055
                  omega
                have d21092 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
                  have r21093 := hand2 (x (-5) 1) (x (-5) 12)
                  have b21094 := hb (x (-5) 12)
                  have b21095 := hb (x (-5) 1 && x (-5) 12)
                  clear * - r21093 b21094 b21095 d21084
                  omega
                have d21096 : (x (-8) 4).toNat = 1 := by
                  have r21097 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := by have q := hcov11 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21098 := hb (x (-8) 4)
                  have b21099 := hb (x (-4) 11)
                  have b21100 := hb (x (-5) 1 && x (-5) 12)
                  have b21101 := hb (x (-6) 2 && x (-6) 13)
                  have b21102 := hb (x (-7) 3 && x (-7) 14)
                  clear * - r21097 b21098 b21099 b21100 b21101 b21102 d20866 d21092 d20971 d20983
                  omega
                have d21103 : (x (-8) 12).toNat = 1 := by
                  have r21104 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
                  have b21105 := hb (x (-8) 4)
                  have b21106 := hb (x (-8) 12)
                  clear * - r21104 b21105 b21106 d21096
                  omega
                have d21107 : (x (-9) 13).toNat = 0 := by
                  have r21108 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21109 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                  have e21110 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                  have b21111 := hb (x (-11) 3)
                  have b21112 := hb (x (-10) 2)
                  have b21113 := hb (x (-9) 13)
                  have b21114 := hb (x (-8) 12)
                  clear * - r21108 e21109 e21110 b21111 b21112 b21113 b21114 d21103
                  omega
                have d21115 : (x (-9) 2 && x (-9) 13).toNat = 0 := by
                  have r21116 := hand2 (x (-9) 2) (x (-9) 13)
                  have b21117 := hb (x (-9) 13)
                  have b21118 := hb (x (-9) 2 && x (-9) 13)
                  clear * - r21116 b21117 b21118 d21107
                  omega
                have d21119 : (x (-10) 2).toNat = 0 := by
                  have r21120 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21121 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                  have e21122 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                  have b21123 := hb (x (-11) 3)
                  have b21124 := hb (x (-10) 2)
                  have b21125 := hb (x (-9) 13)
                  have b21126 := hb (x (-8) 12)
                  clear * - r21120 e21121 e21122 b21123 b21124 b21125 b21126 d21103 d21107
                  omega
                have d21127 : (x (-10) 2 && x (-10) 13).toNat = 0 := by
                  have r21128 := hand1 (x (-10) 2) (x (-10) 13)
                  have b21129 := hb (x (-10) 2)
                  have b21130 := hb (x (-10) 2 && x (-10) 13)
                  clear * - r21128 b21129 b21130 d21119
                  omega
                have d21131 : (x (-10) 2 && x (-10) 11).toNat = 0 := by
                  have r21132 := hand1 (x (-10) 2) (x (-10) 11)
                  have b21133 := hb (x (-10) 2)
                  have b21134 := hb (x (-10) 2 && x (-10) 11)
                  clear * - r21132 b21133 b21134 d21119
                  omega
                have d21135 : (x (-9) 1 && x (-9) 14).toNat = 1 := by
                  have r21136 : 1 ≤ (x (-8) 13).toNat + (x (-9) 1 && x (-9) 14).toNat + (x (-10) 2).toNat := by have q := hcov13 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21137 := hb (x (-10) 2)
                  have b21138 := hb (x (-8) 13)
                  have b21139 := hb (x (-9) 1 && x (-9) 14)
                  clear * - r21136 b21137 b21138 b21139 d21072 d21119
                  omega
                have d21140 : (x (-9) 14).toNat = 1 := by
                  have r21141 := hand2 (x (-9) 1) (x (-9) 14)
                  have b21142 := hb (x (-9) 14)
                  have b21143 := hb (x (-9) 1 && x (-9) 14)
                  clear * - r21141 b21142 b21143 d21135
                  omega
                have d21144 : (x (-10) 1).toNat = 0 := by
                  have r21145 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21146 := hb (x (-10) 1)
                  have b21147 := hb (x (-9) 14)
                  clear * - r21145 b21146 b21147 d21140
                  omega
                have d21148 : (x (-10) 1 && x (-10) 14).toNat = 0 := by
                  have r21149 := hand1 (x (-10) 1) (x (-10) 14)
                  have b21150 := hb (x (-10) 1)
                  have b21151 := hb (x (-10) 1 && x (-10) 14)
                  clear * - r21149 b21150 b21151 d21144
                  omega
                have d21152 : (x (-11) 2).toNat = 1 := by
                  have r21153 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21154 := hb (x (-11) 2)
                  have b21155 := hb (x (-9) 13)
                  have b21156 := hb (x (-10) 1 && x (-10) 14)
                  clear * - r21153 b21154 b21155 b21156 d21107 d21148
                  omega
                have d21157 : (x (-11) 14).toNat = 1 := by
                  have r21158 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
                  have b21159 := hb (x (-11) 2)
                  have b21160 := hb (x (-11) 14)
                  clear * - r21158 b21159 b21160 d21152
                  omega
                have d21161 : (x (-12) 1).toNat = 0 := by
                  have r21162 : (x (-11) 14).toNat + (x (-12) 1).toNat = 1 := by have q := hd14 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21163 := hb (x (-12) 1)
                  have b21164 := hb (x (-11) 14)
                  clear * - r21162 b21163 b21164 d21157
                  omega
                have d21165 : (x (-12) 1 && x (-12) 14).toNat = 0 := by
                  have r21166 := hand1 (x (-12) 1) (x (-12) 14)
                  have b21167 := hb (x (-12) 1)
                  have b21168 := hb (x (-12) 1 && x (-12) 14)
                  clear * - r21166 b21167 b21168 d21161
                  omega
                have d21169 : (x (-12) 1 && x (-12) 12).toNat = 0 := by
                  have r21170 := hand1 (x (-12) 1) (x (-12) 12)
                  have b21171 := hb (x (-12) 1)
                  have b21172 := hb (x (-12) 1 && x (-12) 12)
                  clear * - r21170 b21171 b21172 d21161
                  omega
                have d21173 : (x (-12) 13).toNat = 0 := by
                  have r21174 : (x (-12) 13).toNat ≤ (x (-12) 1).toNat := himp _ _ (hp13 (-12))
                  have b21175 := hb (x (-12) 1)
                  have b21176 := hb (x (-12) 13)
                  clear * - r21174 b21175 b21176 d21161
                  omega
                have d21177 : (x (-12) 4 && x (-12) 13).toNat = 0 := by
                  have r21178 := hand2 (x (-12) 4) (x (-12) 13)
                  have b21179 := hb (x (-12) 13)
                  have b21180 := hb (x (-12) 4 && x (-12) 13)
                  clear * - r21178 b21179 b21180 d21173
                  omega
                have d21181 : (x (-9) 12).toNat = 0 := by
                  have r21182 : (x (-9) 12).toNat + (x (-10) 1 && x (-10) 13).toNat + (x (-11) 2 && x (-11) 14).toNat + (x (-12) 3).toNat = 1 := by have q := hd12 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21183 : (x (-10) 1 && x (-10) 13).toNat = (x (-10) 13).toNat := handr _ _ (fun h => hp13 (-10) (h))
                  have e21184 : (x (-11) 2 && x (-11) 14).toNat = (x (-11) 2).toNat := handl _ _ (fun h => hp2 (-11) (h))
                  have b21185 := hb (x (-12) 3)
                  have b21186 := hb (x (-11) 2)
                  have b21187 := hb (x (-10) 13)
                  have b21188 := hb (x (-9) 12)
                  clear * - r21182 e21183 e21184 b21185 b21186 b21187 b21188 d21152
                  omega
                have d21189 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
                  have r21190 := hand2 (x (-9) 1) (x (-9) 12)
                  have b21191 := hb (x (-9) 12)
                  have b21192 := hb (x (-9) 1 && x (-9) 12)
                  clear * - r21190 b21191 b21192 d21181
                  omega
                have d21193 : (x (-11) 3).toNat = 0 := by
                  have r21194 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := by have q := hd12 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21195 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
                  have e21196 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
                  have b21197 := hb (x (-11) 3)
                  have b21198 := hb (x (-10) 2)
                  have b21199 := hb (x (-9) 13)
                  have b21200 := hb (x (-8) 12)
                  clear * - r21194 e21195 e21196 b21197 b21198 b21199 b21200 d21103 d21107 d21119
                  omega
                have d21201 : (x (-11) 3 && x (-11) 14).toNat = 0 := by
                  have r21202 := hand1 (x (-11) 3) (x (-11) 14)
                  have b21203 := hb (x (-11) 3)
                  have b21204 := hb (x (-11) 3 && x (-11) 14)
                  clear * - r21202 b21203 b21204 d21193
                  omega
                have d21205 : (x (-11) 3 && x (-11) 12).toNat = 0 := by
                  have r21206 := hand1 (x (-11) 3) (x (-11) 12)
                  have b21207 := hb (x (-11) 3)
                  have b21208 := hb (x (-11) 3 && x (-11) 12)
                  clear * - r21206 b21207 b21208 d21193
                  omega
                have d21209 : (x (-11) 11).toNat = 0 := by
                  have r21210 : (x (-11) 11).toNat ≤ (x (-11) 3).toNat := himp _ _ (hp11 (-11))
                  have b21211 := hb (x (-11) 3)
                  have b21212 := hb (x (-11) 11)
                  clear * - r21210 b21211 b21212 d21193
                  omega
                have d21213 : (x (-5) 2 && x (-5) 12).toNat = 0 := by
                  have r21214 := hand2 (x (-5) 2) (x (-5) 12)
                  have b21215 := hb (x (-5) 12)
                  have b21216 := hb (x (-5) 2 && x (-5) 12)
                  clear * - r21214 b21215 b21216 d21084
                  omega
                have d21217 : (x (-6) 13).toNat = 0 := by
                  have r21218 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21219 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                  have e21220 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                  have b21221 := hb (x (-8) 3)
                  have b21222 := hb (x (-7) 2)
                  have b21223 := hb (x (-6) 13)
                  have b21224 := hb (x (-5) 12)
                  clear * - r21218 e21219 e21220 b21221 b21222 b21223 b21224 d21084 d21055
                  omega
                have d21225 : (x (-6) 3 && x (-6) 13).toNat = 0 := by
                  have r21226 := hand2 (x (-6) 3) (x (-6) 13)
                  have b21227 := hb (x (-6) 13)
                  have b21228 := hb (x (-6) 3 && x (-6) 13)
                  clear * - r21226 b21227 b21228 d21217
                  omega
                have d21229 : (x (-7) 4 && x (-7) 14).toNat = 1 := by
                  have r21230 : 1 ≤ (x (-3) 10).toNat + (x (-4) 1 && x (-4) 11).toNat + (x (-5) 2 && x (-5) 12).toNat + (x (-6) 3 && x (-6) 13).toNat + (x (-7) 4 && x (-7) 14).toNat + (x (-8) 5).toNat := by have q := hcov10 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21231 := hb (x (-8) 5)
                  have b21232 := hb (x (-3) 10)
                  have b21233 := hb (x (-4) 1 && x (-4) 11)
                  have b21234 := hb (x (-5) 2 && x (-5) 12)
                  have b21235 := hb (x (-6) 3 && x (-6) 13)
                  have b21236 := hb (x (-7) 4 && x (-7) 14)
                  clear * - r21230 b21231 b21232 b21233 b21234 b21235 b21236 d20850 d20882 d21213 d21225 d21076
                  omega
                have d21237 : (x (-7) 4).toNat = 1 := by
                  have r21238 := hand1 (x (-7) 4) (x (-7) 14)
                  have b21239 := hb (x (-7) 4)
                  have b21240 := hb (x (-7) 4 && x (-7) 14)
                  clear * - r21238 b21239 b21240 d21229
                  omega
                have d21241 : (x (-7) 12).toNat = 1 := by
                  have r21242 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
                  have b21243 := hb (x (-7) 4)
                  have b21244 := hb (x (-7) 12)
                  clear * - r21242 b21243 b21244 d21237
                  omega
                have d21245 : (x (-9) 2).toNat = 0 := by
                  have r21246 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21247 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                  have e21248 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                  have b21249 := hb (x (-10) 3)
                  have b21250 := hb (x (-9) 2)
                  have b21251 := hb (x (-8) 13)
                  have b21252 := hb (x (-7) 12)
                  clear * - r21246 e21247 e21248 b21249 b21250 b21251 b21252 d21241 d21072
                  omega
                have d21253 : (x (-9) 10).toNat = 0 := by
                  have r21254 : (x (-9) 10).toNat ≤ (x (-9) 2).toNat := himp _ _ (hp10 (-9))
                  have b21255 := hb (x (-9) 2)
                  have b21256 := hb (x (-9) 10)
                  clear * - r21254 b21255 b21256 d21245
                  omega
                have d21257 : (x (-9) 1 && x (-9) 10).toNat = 0 := by
                  have r21258 := hand2 (x (-9) 1) (x (-9) 10)
                  have b21259 := hb (x (-9) 10)
                  have b21260 := hb (x (-9) 1 && x (-9) 10)
                  clear * - r21258 b21259 b21260 d21253
                  omega
                have d21261 : (x (-10) 3).toNat = 0 := by
                  have r21262 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := by have q := hd12 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21263 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
                  have e21264 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
                  have b21265 := hb (x (-10) 3)
                  have b21266 := hb (x (-9) 2)
                  have b21267 := hb (x (-8) 13)
                  have b21268 := hb (x (-7) 12)
                  clear * - r21262 e21263 e21264 b21265 b21266 b21267 b21268 d21241 d21072 d21245
                  omega
                have d21269 : (x (-10) 3 && x (-10) 14).toNat = 0 := by
                  have r21270 := hand1 (x (-10) 3) (x (-10) 14)
                  have b21271 := hb (x (-10) 3)
                  have b21272 := hb (x (-10) 3 && x (-10) 14)
                  clear * - r21270 b21271 b21272 d21261
                  omega
                have d21273 : (x (-11) 4).toNat = 1 := by
                  have r21274 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := by have q := hcov11 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21275 := hb (x (-11) 4)
                  have b21276 := hb (x (-7) 11)
                  have b21277 := hb (x (-8) 1 && x (-8) 12)
                  have b21278 := hb (x (-9) 2 && x (-9) 13)
                  have b21279 := hb (x (-10) 3 && x (-10) 14)
                  clear * - r21274 b21275 b21276 b21277 b21278 b21279 d20987 d21068 d21115 d21269
                  omega
                have d21280 : (x (-11) 12).toNat = 1 := by
                  have r21281 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
                  have b21282 := hb (x (-11) 4)
                  have b21283 := hb (x (-11) 12)
                  clear * - r21281 b21282 b21283 d21273
                  omega
                have d21284 : (x (-13) 2).toNat = 0 := by
                  have r21285 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21286 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
                  have e21287 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
                  have b21288 := hb (x (-14) 3)
                  have b21289 := hb (x (-13) 2)
                  have b21290 := hb (x (-12) 13)
                  have b21291 := hb (x (-11) 12)
                  clear * - r21285 e21286 e21287 b21288 b21289 b21290 b21291 d21280 d21173
                  omega
                have d21292 : (x (-13) 2 && x (-13) 13).toNat = 0 := by
                  have r21293 := hand1 (x (-13) 2) (x (-13) 13)
                  have b21294 := hb (x (-13) 2)
                  have b21295 := hb (x (-13) 2 && x (-13) 13)
                  clear * - r21293 b21294 b21295 d21284
                  omega
                have d21296 : (x (-11) 13).toNat = 1 := by
                  have r21297 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21298 := hb (x (-13) 2)
                  have b21299 := hb (x (-11) 13)
                  have b21300 := hb (x (-12) 1 && x (-12) 14)
                  clear * - r21297 b21298 b21299 b21300 d21165 d21284
                  omega
                have d21301 : (x (-10) 12).toNat = 0 := by
                  have r21302 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21303 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
                  have e21304 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
                  have b21305 := hb (x (-13) 3)
                  have b21306 := hb (x (-12) 2)
                  have b21307 := hb (x (-11) 13)
                  have b21308 := hb (x (-10) 12)
                  clear * - r21302 e21303 e21304 b21305 b21306 b21307 b21308 d21296
                  omega
                have d21309 : (x (-12) 2).toNat = 0 := by
                  have r21310 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21311 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
                  have e21312 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
                  have b21313 := hb (x (-13) 3)
                  have b21314 := hb (x (-12) 2)
                  have b21315 := hb (x (-11) 13)
                  have b21316 := hb (x (-10) 12)
                  clear * - r21310 e21311 e21312 b21313 b21314 b21315 b21316 d21301 d21296
                  omega
                have d21317 : (x (-12) 10).toNat = 0 := by
                  have r21318 : (x (-12) 10).toNat ≤ (x (-12) 2).toNat := himp _ _ (hp10 (-12))
                  have b21319 := hb (x (-12) 2)
                  have b21320 := hb (x (-12) 10)
                  clear * - r21318 b21319 b21320 d21309
                  omega
                have d21321 : (x (-13) 3).toNat = 0 := by
                  have r21322 : (x (-10) 12).toNat + (x (-11) 1 && x (-11) 13).toNat + (x (-12) 2 && x (-12) 14).toNat + (x (-13) 3).toNat = 1 := by have q := hd12 (-10); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21323 : (x (-11) 1 && x (-11) 13).toNat = (x (-11) 13).toNat := handr _ _ (fun h => hp13 (-11) (h))
                  have e21324 : (x (-12) 2 && x (-12) 14).toNat = (x (-12) 2).toNat := handl _ _ (fun h => hp2 (-12) (h))
                  have b21325 := hb (x (-13) 3)
                  have b21326 := hb (x (-12) 2)
                  have b21327 := hb (x (-11) 13)
                  have b21328 := hb (x (-10) 12)
                  clear * - r21322 e21323 e21324 b21325 b21326 b21327 b21328 d21301 d21296 d21309
                  omega
                have d21329 : (x (-13) 11).toNat = 0 := by
                  have r21330 : (x (-13) 11).toNat ≤ (x (-13) 3).toNat := himp _ _ (hp11 (-13))
                  have b21331 := hb (x (-13) 3)
                  have b21332 := hb (x (-13) 11)
                  clear * - r21330 b21331 b21332 d21321
                  omega
                have d21333 : (x (-13) 1 && x (-13) 11).toNat = 0 := by
                  have r21334 := hand2 (x (-13) 1) (x (-13) 11)
                  have b21335 := hb (x (-13) 11)
                  have b21336 := hb (x (-13) 1 && x (-13) 11)
                  clear * - r21334 b21335 b21336 d21329
                  omega
                have d21337 : (x (-14) 3).toNat = 0 := by
                  have r21338 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21339 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
                  have e21340 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
                  have b21341 := hb (x (-14) 3)
                  have b21342 := hb (x (-13) 2)
                  have b21343 := hb (x (-12) 13)
                  have b21344 := hb (x (-11) 12)
                  clear * - r21338 e21339 e21340 b21341 b21342 b21343 b21344 d21280 d21173 d21284
                  omega
                have d21345 : (x (-14) 3 && x (-14) 14).toNat = 0 := by
                  have r21346 := hand1 (x (-14) 3) (x (-14) 14)
                  have b21347 := hb (x (-14) 3)
                  have b21348 := hb (x (-14) 3 && x (-14) 14)
                  clear * - r21346 b21347 b21348 d21337
                  omega
                have d21349 : (x (-15) 4).toNat = 1 := by
                  have r21350 : 1 ≤ (x (-11) 11).toNat + (x (-12) 1 && x (-12) 12).toNat + (x (-13) 2 && x (-13) 13).toNat + (x (-14) 3 && x (-14) 14).toNat + (x (-15) 4).toNat := by have q := hcov11 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21351 := hb (x (-15) 4)
                  have b21352 := hb (x (-11) 11)
                  have b21353 := hb (x (-12) 1 && x (-12) 12)
                  have b21354 := hb (x (-13) 2 && x (-13) 13)
                  have b21355 := hb (x (-14) 3 && x (-14) 14)
                  clear * - r21350 b21351 b21352 b21353 b21354 b21355 d21209 d21169 d21292 d21345
                  omega
                have d21356 : (x (-15) 12).toNat = 1 := by
                  have r21357 : (x (-15) 4).toNat ≤ (x (-15) 12).toNat := himp _ _ (hp4 (-15))
                  have b21358 := hb (x (-15) 4)
                  have b21359 := hb (x (-15) 12)
                  clear * - r21357 b21358 b21359 d21349
                  omega
                have d21360 : (x (-16) 13).toNat = 0 := by
                  have r21361 : (x (-15) 12).toNat + (x (-16) 1 && x (-16) 13).toNat + (x (-17) 2 && x (-17) 14).toNat + (x (-18) 3).toNat = 1 := by have q := hd12 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21362 : (x (-16) 1 && x (-16) 13).toNat = (x (-16) 13).toNat := handr _ _ (fun h => hp13 (-16) (h))
                  have e21363 : (x (-17) 2 && x (-17) 14).toNat = (x (-17) 2).toNat := handl _ _ (fun h => hp2 (-17) (h))
                  have b21364 := hb (x (-18) 3)
                  have b21365 := hb (x (-17) 2)
                  have b21366 := hb (x (-16) 13)
                  have b21367 := hb (x (-15) 12)
                  clear * - r21361 e21362 e21363 b21364 b21365 b21366 b21367 d21356
                  omega
                have d21368 : (x (-17) 2).toNat = 0 := by
                  have r21369 : (x (-15) 12).toNat + (x (-16) 1 && x (-16) 13).toNat + (x (-17) 2 && x (-17) 14).toNat + (x (-18) 3).toNat = 1 := by have q := hd12 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21370 : (x (-16) 1 && x (-16) 13).toNat = (x (-16) 13).toNat := handr _ _ (fun h => hp13 (-16) (h))
                  have e21371 : (x (-17) 2 && x (-17) 14).toNat = (x (-17) 2).toNat := handl _ _ (fun h => hp2 (-17) (h))
                  have b21372 := hb (x (-18) 3)
                  have b21373 := hb (x (-17) 2)
                  have b21374 := hb (x (-16) 13)
                  have b21375 := hb (x (-15) 12)
                  clear * - r21369 e21370 e21371 b21372 b21373 b21374 b21375 d21356 d21360
                  omega
                have d21376 : (x (-8) 3).toNat = 0 := by
                  have r21377 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21378 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
                  have e21379 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
                  have b21380 := hb (x (-8) 3)
                  have b21381 := hb (x (-7) 2)
                  have b21382 := hb (x (-6) 13)
                  have b21383 := hb (x (-5) 12)
                  clear * - r21377 e21378 e21379 b21380 b21381 b21382 b21383 d21084 d21217 d21055
                  omega
                have d21384 : (x (-8) 11).toNat = 0 := by
                  have r21385 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
                  have b21386 := hb (x (-8) 3)
                  have b21387 := hb (x (-8) 11)
                  clear * - r21385 b21386 b21387 d21376
                  omega
                have d21388 : (x (-12) 4).toNat = 1 := by
                  have r21389 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21390 := hb (x (-12) 4)
                  have b21391 := hb (x (-8) 11)
                  have b21392 := hb (x (-9) 1 && x (-9) 12)
                  have b21393 := hb (x (-10) 2 && x (-10) 13)
                  have b21394 := hb (x (-11) 3 && x (-11) 14)
                  clear * - r21389 b21390 b21391 b21392 b21393 b21394 d21384 d21189 d21127 d21201
                  omega
                have d21395 : (x (-12) 12).toNat = 1 := by
                  have r21396 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
                  have b21397 := hb (x (-12) 4)
                  have b21398 := hb (x (-12) 12)
                  clear * - r21396 b21397 b21398 d21388
                  omega
                have d21399 : (x (-13) 13).toNat = 0 := by
                  have r21400 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21401 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
                  have e21402 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
                  have b21403 := hb (x (-15) 3)
                  have b21404 := hb (x (-14) 2)
                  have b21405 := hb (x (-13) 13)
                  have b21406 := hb (x (-12) 12)
                  clear * - r21400 e21401 e21402 b21403 b21404 b21405 b21406 d21395
                  omega
                have d21407 : (x (-13) 5).toNat = 0 := by
                  have r21408 : (x (-13) 5).toNat ≤ (x (-13) 13).toNat := himp _ _ (hp5 (-13))
                  have b21409 := hb (x (-13) 5)
                  have b21410 := hb (x (-13) 13)
                  clear * - r21408 b21409 b21410 d21399
                  omega
                have d21411 : (x (-13) 5 && x (-13) 14).toNat = 0 := by
                  have r21412 := hand1 (x (-13) 5) (x (-13) 14)
                  have b21413 := hb (x (-13) 5)
                  have b21414 := hb (x (-13) 5 && x (-13) 14)
                  clear * - r21412 b21413 b21414 d21407
                  omega
                have d21415 : (x (-14) 6).toNat = 1 := by
                  have r21416 : 1 ≤ (x (-8) 9).toNat + (x (-9) 1 && x (-9) 10).toNat + (x (-10) 2 && x (-10) 11).toNat + (x (-11) 3 && x (-11) 12).toNat + (x (-12) 4 && x (-12) 13).toNat + (x (-13) 5 && x (-13) 14).toNat + (x (-14) 6).toNat := by have q := hcov9 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21417 := hb (x (-14) 6)
                  have b21418 := hb (x (-8) 9)
                  have b21419 := hb (x (-9) 1 && x (-9) 10)
                  have b21420 := hb (x (-10) 2 && x (-10) 11)
                  have b21421 := hb (x (-11) 3 && x (-11) 12)
                  have b21422 := hb (x (-12) 4 && x (-12) 13)
                  have b21423 := hb (x (-13) 5 && x (-13) 14)
                  clear * - r21416 b21417 b21418 b21419 b21420 b21421 b21422 b21423 d21080 d21257 d21131 d21205 d21177 d21411
                  omega
                have d21424 : (x (-14) 14).toNat = 1 := by
                  have r21425 : (x (-14) 6).toNat ≤ (x (-14) 14).toNat := himp _ _ (hp6 (-14))
                  have b21426 := hb (x (-14) 6)
                  have b21427 := hb (x (-14) 14)
                  clear * - r21425 b21426 b21427 d21415
                  omega
                have d21428 : (x (-15) 1).toNat = 0 := by
                  have r21429 : (x (-14) 14).toNat + (x (-15) 1).toNat = 1 := by have q := hd14 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21430 := hb (x (-15) 1)
                  have b21431 := hb (x (-14) 14)
                  clear * - r21429 b21430 b21431 d21424
                  omega
                have d21432 : (x (-15) 13).toNat = 0 := by
                  have r21433 : (x (-15) 13).toNat ≤ (x (-15) 1).toNat := himp _ _ (hp13 (-15))
                  have b21434 := hb (x (-15) 1)
                  have b21435 := hb (x (-15) 13)
                  clear * - r21433 b21434 b21435 d21428
                  omega
                have d21436 : (x (-15) 3 && x (-15) 13).toNat = 0 := by
                  have r21437 := hand2 (x (-15) 3) (x (-15) 13)
                  have b21438 := hb (x (-15) 13)
                  have b21439 := hb (x (-15) 3 && x (-15) 13)
                  clear * - r21437 b21438 b21439 d21432
                  omega
                have d21440 : (x (-16) 1 && x (-16) 14).toNat = 1 := by
                  have r21441 : 1 ≤ (x (-15) 13).toNat + (x (-16) 1 && x (-16) 14).toNat + (x (-17) 2).toNat := by have q := hcov13 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21442 := hb (x (-17) 2)
                  have b21443 := hb (x (-15) 13)
                  have b21444 := hb (x (-16) 1 && x (-16) 14)
                  clear * - r21441 b21442 b21443 b21444 d21432 d21368
                  omega
                have d21445 : (x (-16) 14).toNat = 1 := by
                  have r21446 := hand2 (x (-16) 1) (x (-16) 14)
                  have b21447 := hb (x (-16) 14)
                  have b21448 := hb (x (-16) 1 && x (-16) 14)
                  clear * - r21446 b21447 b21448 d21440
                  omega
                have d21449 : (x (-17) 1).toNat = 0 := by
                  have r21450 : (x (-16) 14).toNat + (x (-17) 1).toNat = 1 := by have q := hd14 (-16); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21451 := hb (x (-17) 1)
                  have b21452 := hb (x (-16) 14)
                  clear * - r21450 b21451 b21452 d21445
                  omega
                have d21453 : (x (-17) 1 && x (-17) 14).toNat = 0 := by
                  have r21454 := hand1 (x (-17) 1) (x (-17) 14)
                  have b21455 := hb (x (-17) 1)
                  have b21456 := hb (x (-17) 1 && x (-17) 14)
                  clear * - r21454 b21455 b21456 d21449
                  omega
                have d21457 : (x (-18) 2).toNat = 1 := by
                  have r21458 : 1 ≤ (x (-16) 13).toNat + (x (-17) 1 && x (-17) 14).toNat + (x (-18) 2).toNat := by have q := hcov13 (-16); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21459 := hb (x (-18) 2)
                  have b21460 := hb (x (-16) 13)
                  have b21461 := hb (x (-17) 1 && x (-17) 14)
                  clear * - r21458 b21459 b21460 b21461 d21360 d21453
                  omega
                have d21462 : (x (-16) 12).toNat = 0 := by
                  have r21463 : (x (-16) 12).toNat + (x (-17) 1 && x (-17) 13).toNat + (x (-18) 2 && x (-18) 14).toNat + (x (-19) 3).toNat = 1 := by have q := hd12 (-16); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21464 : (x (-17) 1 && x (-17) 13).toNat = (x (-17) 13).toNat := handr _ _ (fun h => hp13 (-17) (h))
                  have e21465 : (x (-18) 2 && x (-18) 14).toNat = (x (-18) 2).toNat := handl _ _ (fun h => hp2 (-18) (h))
                  have b21466 := hb (x (-19) 3)
                  have b21467 := hb (x (-18) 2)
                  have b21468 := hb (x (-17) 13)
                  have b21469 := hb (x (-16) 12)
                  clear * - r21463 e21464 e21465 b21466 b21467 b21468 b21469 d21457
                  omega
                have d21470 : (x (-16) 4).toNat = 0 := by
                  have r21471 : (x (-16) 4).toNat ≤ (x (-16) 12).toNat := himp _ _ (hp4 (-16))
                  have b21472 := hb (x (-16) 4)
                  have b21473 := hb (x (-16) 12)
                  clear * - r21471 b21472 b21473 d21462
                  omega
                have d21474 : (x (-16) 4 && x (-16) 14).toNat = 0 := by
                  have r21475 := hand1 (x (-16) 4) (x (-16) 14)
                  have b21476 := hb (x (-16) 4)
                  have b21477 := hb (x (-16) 4 && x (-16) 14)
                  clear * - r21475 b21476 b21477 d21470
                  omega
                have d21478 : (x (-17) 13).toNat = 0 := by
                  have r21479 : (x (-16) 12).toNat + (x (-17) 1 && x (-17) 13).toNat + (x (-18) 2 && x (-18) 14).toNat + (x (-19) 3).toNat = 1 := by have q := hd12 (-16); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e21480 : (x (-17) 1 && x (-17) 13).toNat = (x (-17) 13).toNat := handr _ _ (fun h => hp13 (-17) (h))
                  have e21481 : (x (-18) 2 && x (-18) 14).toNat = (x (-18) 2).toNat := handl _ _ (fun h => hp2 (-18) (h))
                  have b21482 := hb (x (-19) 3)
                  have b21483 := hb (x (-18) 2)
                  have b21484 := hb (x (-17) 13)
                  have b21485 := hb (x (-16) 12)
                  clear * - r21479 e21480 e21481 b21482 b21483 b21484 b21485 d21462 d21457
                  omega
                have d21486 : (x (-17) 5).toNat = 0 := by
                  have r21487 : (x (-17) 5).toNat ≤ (x (-17) 13).toNat := himp _ _ (hp5 (-17))
                  have b21488 := hb (x (-17) 5)
                  have b21489 := hb (x (-17) 13)
                  clear * - r21487 b21488 b21489 d21478
                  omega
                have d21490 : (x (-14) 2 && x (-14) 12).toNat = 1 := by
                  have r21491 : 1 ≤ (x (-12) 10).toNat + (x (-13) 1 && x (-13) 11).toNat + (x (-14) 2 && x (-14) 12).toNat + (x (-15) 3 && x (-15) 13).toNat + (x (-16) 4 && x (-16) 14).toNat + (x (-17) 5).toNat := by have q := hcov10 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b21492 := hb (x (-17) 5)
                  have b21493 := hb (x (-12) 10)
                  have b21494 := hb (x (-13) 1 && x (-13) 11)
                  have b21495 := hb (x (-14) 2 && x (-14) 12)
                  have b21496 := hb (x (-15) 3 && x (-15) 13)
                  have b21497 := hb (x (-16) 4 && x (-16) 14)
                  clear * - r21491 b21492 b21493 b21494 b21495 b21496 b21497 d21317 d21333 d21436 d21474 d21486
                  omega
                have d21498 : (x (-14) 2).toNat = 1 := by
                  have r21499 := hand1 (x (-14) 2) (x (-14) 12)
                  have b21500 := hb (x (-14) 2)
                  have b21501 := hb (x (-14) 2 && x (-14) 12)
                  clear * - r21499 b21500 b21501 d21490
                  omega
                have r21502 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21503 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
                have e21504 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
                have b21505 := hb (x (-15) 3)
                have b21506 := hb (x (-14) 2)
                have b21507 := hb (x (-13) 13)
                have b21508 := hb (x (-12) 12)
                linarith only [r21502, e21503, e21504, b21505, b21506, b21507, b21508, d21395, d21399, d21498]
            · have f21509 : (x 1 7).toNat = 1 := by rw [h19766]; rfl
              have d21510 : (x 8 8).toNat = 0 := by
                have r21511 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21512 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e21513 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e21514 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e21515 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e21516 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e21517 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b21518 := hb (x 1 7)
                have b21519 := hb (x 2 6)
                have b21520 := hb (x 3 5)
                have b21521 := hb (x 4 4)
                have b21522 := hb (x 5 11)
                have b21523 := hb (x 6 10)
                have b21524 := hb (x 7 9)
                have b21525 := hb (x 8 8)
                clear * - r21511 e21512 e21513 e21514 e21515 e21516 e21517 b21518 b21519 b21520 b21521 b21522 b21523 b21524 b21525 d19573 d19589 f21509
                omega
              have d21526 : (x 7 9).toNat = 0 := by
                have r21527 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21528 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e21529 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e21530 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e21531 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e21532 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e21533 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b21534 := hb (x 1 7)
                have b21535 := hb (x 2 6)
                have b21536 := hb (x 3 5)
                have b21537 := hb (x 4 4)
                have b21538 := hb (x 5 11)
                have b21539 := hb (x 6 10)
                have b21540 := hb (x 7 9)
                have b21541 := hb (x 8 8)
                clear * - r21527 e21528 e21529 e21530 e21531 e21532 e21533 b21534 b21535 b21536 b21537 b21538 b21539 b21540 b21541 d21510 d19573 d19589 f21509
                omega
              have d21542 : (x 6 10).toNat = 0 := by
                have r21543 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e21544 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
                have e21545 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
                have e21546 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
                have e21547 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
                have e21548 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
                have e21549 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
                have b21550 := hb (x 1 7)
                have b21551 := hb (x 2 6)
                have b21552 := hb (x 3 5)
                have b21553 := hb (x 4 4)
                have b21554 := hb (x 5 11)
                have b21555 := hb (x 6 10)
                have b21556 := hb (x 7 9)
                have b21557 := hb (x 8 8)
                clear * - r21543 e21544 e21545 e21546 e21547 e21548 e21549 b21550 b21551 b21552 b21553 b21554 b21555 b21556 b21557 d21510 d21526 d19573 d19589 f21509
                omega
              have d21558 : (x 6 1 && x 6 10).toNat = 0 := by
                have r21559 := hand2 (x 6 1) (x 6 10)
                have b21560 := hb (x 6 10)
                have b21561 := hb (x 6 1 && x 6 10)
                clear * - r21559 b21560 b21561 d21542
                omega
              have d21562 : (x 5 2 && x 5 11).toNat = 1 := by
                have r21563 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b21564 := hb (x 1 6)
                have b21565 := hb (x 7 9)
                have b21566 := hb (x 6 1 && x 6 10)
                have b21567 := hb (x 5 2 && x 5 11)
                have b21568 := hb (x 4 3 && x 4 12)
                have b21569 := hb (x 3 4 && x 3 13)
                have b21570 := hb (x 2 5 && x 2 14)
                clear * - r21563 b21564 b21565 b21566 b21567 b21568 b21569 b21570 d21526 d21558 d19569 g22 g23 g5
                omega
              have d21571 : (x 5 11).toNat = 1 := by
                have r21572 := hand2 (x 5 2) (x 5 11)
                have b21573 := hb (x 5 11)
                have b21574 := hb (x 5 2 && x 5 11)
                clear * - r21572 b21573 b21574 d21562
                omega
              have r21575 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21576 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
              have e21577 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
              have e21578 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
              have e21579 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
              have e21580 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
              have e21581 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
              have b21582 := hb (x 1 7)
              have b21583 := hb (x 2 6)
              have b21584 := hb (x 3 5)
              have b21585 := hb (x 4 4)
              have b21586 := hb (x 5 11)
              have b21587 := hb (x 6 10)
              have b21588 := hb (x 7 9)
              have b21589 := hb (x 8 8)
              linarith only [r21575, e21576, e21577, e21578, e21579, e21580, e21581, b21582, b21583, b21584, b21585, b21586, b21587, b21588, b21589, d21510, d21526, d21542, d21571, d19573, d19589, f21509]
          · have f21590 : (x (-1) 6).toNat = 1 := by rw [h19760]; rfl
            have d21591 : (x (-1) 14).toNat = 1 := by
              have r21592 : (x (-1) 6).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp6 (-1))
              have b21593 := hb (x (-1) 6)
              have b21594 := hb (x (-1) 14)
              clear * - r21592 b21593 b21594 f21590
              omega
            have d21595 : (x (-2) 1).toNat = 0 := by
              have r21596 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21597 := hb (x (-2) 1)
              have b21598 := hb (x (-1) 14)
              clear * - r21596 b21597 b21598 d21591
              omega
            have d21599 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
              have r21600 := hand1 (x (-2) 1) (x (-2) 14)
              have b21601 := hb (x (-2) 1)
              have b21602 := hb (x (-2) 1 && x (-2) 14)
              clear * - r21600 b21601 b21602 d21595
              omega
            have d21603 : (x (-2) 13).toNat = 0 := by
              have r21604 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
              have b21605 := hb (x (-2) 1)
              have b21606 := hb (x (-2) 13)
              clear * - r21604 b21605 b21606 d21595
              omega
            have d21607 : (x (-2) 5).toNat = 0 := by
              have r21608 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
              have b21609 := hb (x (-2) 5)
              have b21610 := hb (x (-2) 13)
              clear * - r21608 b21609 b21610 d21603
              omega
            have d21611 : (x 5 8).toNat = 0 := by
              have r21612 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21613 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e21614 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e21615 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e21616 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e21617 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e21618 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have b21619 := hb (x (-2) 7)
              have b21620 := hb (x (-1) 6)
              have b21621 := hb (x 0 5)
              have b21622 := hb (x 1 4)
              have b21623 := hb (x 2 11)
              have b21624 := hb (x 3 10)
              have b21625 := hb (x 4 9)
              have b21626 := hb (x 5 8)
              clear * - r21612 e21613 e21614 e21615 e21616 e21617 e21618 b21619 b21620 b21621 b21622 b21623 b21624 b21625 b21626 d19452 f19755 g0 f21590
              omega
            have d21627 : (x 4 9).toNat = 0 := by
              have r21628 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21629 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e21630 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e21631 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e21632 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e21633 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e21634 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have b21635 := hb (x (-2) 7)
              have b21636 := hb (x (-1) 6)
              have b21637 := hb (x 0 5)
              have b21638 := hb (x 1 4)
              have b21639 := hb (x 2 11)
              have b21640 := hb (x 3 10)
              have b21641 := hb (x 4 9)
              have b21642 := hb (x 5 8)
              clear * - r21628 e21629 e21630 e21631 e21632 e21633 e21634 b21635 b21636 b21637 b21638 b21639 b21640 b21641 b21642 d21611 d19452 f19755 g0 f21590
              omega
            have d21643 : (x 2 11).toNat = 0 := by
              have r21644 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21645 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
              have e21646 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
              have e21647 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
              have e21648 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
              have e21649 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
              have e21650 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
              have b21651 := hb (x (-2) 7)
              have b21652 := hb (x (-1) 6)
              have b21653 := hb (x 0 5)
              have b21654 := hb (x 1 4)
              have b21655 := hb (x 2 11)
              have b21656 := hb (x 3 10)
              have b21657 := hb (x 4 9)
              have b21658 := hb (x 5 8)
              clear * - r21644 e21645 e21646 e21647 e21648 e21649 e21650 b21651 b21652 b21653 b21654 b21655 b21656 b21657 b21658 d21611 d21627 d19452 f19755 g0 f21590
              omega
            have d21659 : (x 2 1 && x 2 11).toNat = 0 := by
              have r21660 := hand2 (x 2 1) (x 2 11)
              have b21661 := hb (x 2 11)
              have b21662 := hb (x 2 1 && x 2 11)
              clear * - r21660 b21661 b21662 d21643
              omega
            have d21663 : (x (-1) 4 && x (-1) 14).toNat = 1 := by
              have r21664 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21665 := hb (x (-2) 5)
              have b21666 := hb (x 3 10)
              have b21667 := hb (x 2 1 && x 2 11)
              have b21668 := hb (x 1 2 && x 1 12)
              have b21669 := hb (x 0 3 && x 0 13)
              have b21670 := hb (x (-1) 4 && x (-1) 14)
              clear * - r21664 b21665 b21666 b21667 b21668 b21669 b21670 d19452 d21659 g24 g25 d21607
              omega
            have d21671 : (x (-1) 4).toNat = 1 := by
              have r21672 := hand1 (x (-1) 4) (x (-1) 14)
              have b21673 := hb (x (-1) 4)
              have b21674 := hb (x (-1) 4 && x (-1) 14)
              clear * - r21672 b21673 b21674 d21663
              omega
            have d21675 : (x (-1) 12).toNat = 1 := by
              have r21676 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
              have b21677 := hb (x (-1) 4)
              have b21678 := hb (x (-1) 12)
              clear * - r21676 b21677 b21678 d21671
              omega
            have d21679 : (x (-3) 2).toNat = 0 := by
              have r21680 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21681 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e21682 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b21683 := hb (x (-4) 3)
              have b21684 := hb (x (-3) 2)
              have b21685 := hb (x (-2) 13)
              have b21686 := hb (x (-1) 12)
              clear * - r21680 e21681 e21682 b21683 b21684 b21685 b21686 d21675 d21603
              omega
            have d21687 : (x (-1) 13).toNat = 1 := by
              have r21688 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21689 := hb (x (-3) 2)
              have b21690 := hb (x (-1) 13)
              have b21691 := hb (x (-2) 1 && x (-2) 14)
              clear * - r21688 b21689 b21690 b21691 d21599 d21679
              omega
            have d21692 : (x (-2) 2).toNat = 0 := by
              have r21693 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e21694 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
              have e21695 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
              have b21696 := hb (x (-3) 3)
              have b21697 := hb (x (-2) 2)
              have b21698 := hb (x (-1) 13)
              have b21699 := hb (x 0 12)
              clear * - r21693 e21694 e21695 b21696 b21697 b21698 b21699 f19749 d21687
              omega
            have d21700 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
              have r21701 := hand1 (x (-2) 2) (x (-2) 12)
              have b21702 := hb (x (-2) 2)
              have b21703 := hb (x (-2) 2 && x (-2) 12)
              clear * - r21701 b21702 b21703 d21692
              omega
            have d21704 : (x (-3) 3 && x (-3) 13).toNat = 1 := by
              have r21705 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b21706 := hb (x (-5) 5)
              have b21707 := hb (x 0 10)
              have b21708 := hb (x (-1) 1 && x (-1) 11)
              have b21709 := hb (x (-2) 2 && x (-2) 12)
              have b21710 := hb (x (-3) 3 && x (-3) 13)
              have b21711 := hb (x (-4) 4 && x (-4) 14)
              clear * - r21705 b21706 b21707 b21708 b21709 b21710 b21711 d19415 d19638 d21700 d19329 d19341
              omega
            have d21712 : (x (-3) 3).toNat = 1 := by
              have r21713 := hand1 (x (-3) 3) (x (-3) 13)
              have b21714 := hb (x (-3) 3)
              have b21715 := hb (x (-3) 3 && x (-3) 13)
              clear * - r21713 b21714 b21715 d21704
              omega
            have r21716 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21717 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
            have e21718 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
            have b21719 := hb (x (-3) 3)
            have b21720 := hb (x (-2) 2)
            have b21721 := hb (x (-1) 13)
            have b21722 := hb (x 0 12)
            linarith only [r21716, e21717, e21718, b21719, b21720, b21721, b21722, f19749, d21687, d21692, d21712]
        · have f21723 : (x 1 4).toNat = 1 := by rw [h19754]; rfl
          have d21724 : (x 1 12).toNat = 1 := by
            have r21725 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
            have b21726 := hb (x 1 4)
            have b21727 := hb (x 1 12)
            clear * - r21725 b21726 b21727 f21723
            omega
          have d21728 : (x (-1) 2).toNat = 0 := by
            have r21729 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21730 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e21731 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b21732 := hb (x (-2) 3)
            have b21733 := hb (x (-1) 2)
            have b21734 := hb (x 0 13)
            have b21735 := hb (x 1 12)
            clear * - r21729 e21730 e21731 b21732 b21733 b21734 b21735 d21724 g3
            omega
          have d21736 : (x (-1) 2 && x (-1) 13).toNat = 0 := by
            have r21737 := hand1 (x (-1) 2) (x (-1) 13)
            have b21738 := hb (x (-1) 2)
            have b21739 := hb (x (-1) 2 && x (-1) 13)
            clear * - r21737 b21738 b21739 d21728
            omega
          have d21740 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
            have r21741 := hand1 (x (-1) 2) (x (-1) 12)
            have b21742 := hb (x (-1) 2)
            have b21743 := hb (x (-1) 2 && x (-1) 12)
            clear * - r21741 b21742 b21743 d21728
            omega
          have d21744 : (x 0 1 && x 0 14).toNat = 1 := by
            have r21745 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21746 := hb (x (-1) 2)
            have b21747 := hb (x 1 13)
            have b21748 := hb (x 0 1 && x 0 14)
            clear * - r21745 b21746 b21747 b21748 d19549 d21728
            omega
          have d21749 : (x 0 14).toNat = 1 := by
            have r21750 := hand2 (x 0 1) (x 0 14)
            have b21751 := hb (x 0 14)
            have b21752 := hb (x 0 1 && x 0 14)
            clear * - r21750 b21751 b21752 d21744
            omega
          have d21753 : (x (-1) 1).toNat = 0 := by
            have r21754 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21755 := hb (x (-1) 1)
            have b21756 := hb (x 0 14)
            clear * - r21754 b21755 b21756 d21749
            omega
          have d21757 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
            have r21758 := hand1 (x (-1) 1) (x (-1) 14)
            have b21759 := hb (x (-1) 1)
            have b21760 := hb (x (-1) 1 && x (-1) 14)
            clear * - r21758 b21759 b21760 d21753
            omega
          have d21761 : (x (-2) 2).toNat = 1 := by
            have r21762 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21763 := hb (x (-2) 2)
            have b21764 := hb (x 0 13)
            have b21765 := hb (x (-1) 1 && x (-1) 14)
            clear * - r21762 b21763 b21764 b21765 g3 d21757
            omega
          have d21766 : (x (-2) 14).toNat = 1 := by
            have r21767 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
            have b21768 := hb (x (-2) 2)
            have b21769 := hb (x (-2) 14)
            clear * - r21767 b21768 b21769 d21761
            omega
          have d21770 : (x (-3) 1).toNat = 0 := by
            have r21771 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21772 := hb (x (-3) 1)
            have b21773 := hb (x (-2) 14)
            clear * - r21771 b21772 b21773 d21766
            omega
          have d21774 : (x (-3) 13).toNat = 0 := by
            have r21775 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
            have b21776 := hb (x (-3) 1)
            have b21777 := hb (x (-3) 13)
            clear * - r21775 b21776 b21777 d21770
            omega
          have d21778 : (x (-2) 3).toNat = 0 := by
            have r21779 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21780 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e21781 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b21782 := hb (x (-2) 3)
            have b21783 := hb (x (-1) 2)
            have b21784 := hb (x 0 13)
            have b21785 := hb (x 1 12)
            clear * - r21779 e21780 e21781 b21782 b21783 b21784 b21785 d21724 g3 d21728
            omega
          have d21786 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
            have r21787 := hand1 (x (-2) 3) (x (-2) 14)
            have b21788 := hb (x (-2) 3)
            have b21789 := hb (x (-2) 3 && x (-2) 14)
            clear * - r21787 b21788 b21789 d21778
            omega
          have d21790 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
            have r21791 := hand1 (x (-2) 3) (x (-2) 13)
            have b21792 := hb (x (-2) 3)
            have b21793 := hb (x (-2) 3 && x (-2) 13)
            clear * - r21791 b21792 b21793 d21778
            omega
          have d21794 : (x (-3) 4).toNat = 1 := by
            have r21795 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21796 := hb (x (-3) 4)
            have b21797 := hb (x 1 11)
            have b21798 := hb (x 0 1 && x 0 12)
            have b21799 := hb (x (-1) 2 && x (-1) 13)
            have b21800 := hb (x (-2) 3 && x (-2) 14)
            clear * - r21795 b21796 b21797 b21798 b21799 b21800 d19605 d19750 d21736 d21786
            omega
          have d21801 : (x (-3) 12).toNat = 1 := by
            have r21802 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
            have b21803 := hb (x (-3) 4)
            have b21804 := hb (x (-3) 12)
            clear * - r21802 b21803 b21804 d21794
            omega
          have d21805 : (x (-4) 13).toNat = 0 := by
            have r21806 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21807 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e21808 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b21809 := hb (x (-6) 3)
            have b21810 := hb (x (-5) 2)
            have b21811 := hb (x (-4) 13)
            have b21812 := hb (x (-3) 12)
            clear * - r21806 e21807 e21808 b21809 b21810 b21811 b21812 d21801
            omega
          have d21813 : (x (-4) 5).toNat = 0 := by
            have r21814 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
            have b21815 := hb (x (-4) 5)
            have b21816 := hb (x (-4) 13)
            clear * - r21814 b21815 b21816 d21805
            omega
          have d21817 : (x (-5) 2).toNat = 0 := by
            have r21818 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e21819 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e21820 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b21821 := hb (x (-6) 3)
            have b21822 := hb (x (-5) 2)
            have b21823 := hb (x (-4) 13)
            have b21824 := hb (x (-3) 12)
            clear * - r21818 e21819 e21820 b21821 b21822 b21823 b21824 d21801 d21805
            omega
          have d21825 : (x (-4) 1 && x (-4) 14).toNat = 1 := by
            have r21826 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21827 := hb (x (-5) 2)
            have b21828 := hb (x (-3) 13)
            have b21829 := hb (x (-4) 1 && x (-4) 14)
            clear * - r21826 b21827 b21828 b21829 d21774 d21817
            omega
          have d21830 : (x (-4) 1).toNat = 1 := by
            have r21831 := hand1 (x (-4) 1) (x (-4) 14)
            have b21832 := hb (x (-4) 1)
            have b21833 := hb (x (-4) 1 && x (-4) 14)
            clear * - r21831 b21832 b21833 d21825
            omega
          have d21834 : (x (-3) 14).toNat = 0 := by
            have r21835 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b21836 := hb (x (-4) 1)
            have b21837 := hb (x (-3) 14)
            clear * - r21835 b21836 b21837 d21830
            omega
          have d21838 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
            have r21839 := hand2 (x (-3) 4) (x (-3) 14)
            have b21840 := hb (x (-3) 14)
            have b21841 := hb (x (-3) 4 && x (-3) 14)
            clear * - r21839 b21840 b21841 d21834
            omega
          have r21842 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21843 := hb (x (-4) 5)
          have b21844 := hb (x 1 10)
          have b21845 := hb (x 0 1 && x 0 11)
          have b21846 := hb (x (-1) 2 && x (-1) 12)
          have b21847 := hb (x (-2) 3 && x (-2) 13)
          have b21848 := hb (x (-3) 4 && x (-3) 14)
          linarith only [r21842, b21843, b21844, b21845, b21846, b21847, b21848, g6, d19488, d21740, d21790, d21838, d21813]
      · have f21849 : (x 0 12).toNat = 1 := by rw [h19748]; rfl
        have d21850 : (x (-1) 13).toNat = 0 := by
          have r21851 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21852 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e21853 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b21854 := hb (x (-3) 3)
          have b21855 := hb (x (-2) 2)
          have b21856 := hb (x (-1) 13)
          have b21857 := hb (x 0 12)
          clear * - r21851 e21852 e21853 b21854 b21855 b21856 b21857 f21849
          omega
        have d21858 : (x (-2) 2).toNat = 0 := by
          have r21859 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21860 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e21861 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b21862 := hb (x (-3) 3)
          have b21863 := hb (x (-2) 2)
          have b21864 := hb (x (-1) 13)
          have b21865 := hb (x 0 12)
          clear * - r21859 e21860 e21861 b21862 b21863 b21864 b21865 f21849 d21850
          omega
        have d21866 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
          have r21867 := hand1 (x (-2) 2) (x (-2) 13)
          have b21868 := hb (x (-2) 2)
          have b21869 := hb (x (-2) 2 && x (-2) 13)
          clear * - r21867 b21868 b21869 d21858
          omega
        have d21870 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
          have r21871 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21872 := hb (x (-2) 2)
          have b21873 := hb (x 0 13)
          have b21874 := hb (x (-1) 1 && x (-1) 14)
          clear * - r21871 b21872 b21873 b21874 g3 d21858
          omega
        have d21875 : (x (-1) 14).toNat = 1 := by
          have r21876 := hand2 (x (-1) 1) (x (-1) 14)
          have b21877 := hb (x (-1) 14)
          have b21878 := hb (x (-1) 1 && x (-1) 14)
          clear * - r21876 b21877 b21878 d21870
          omega
        have d21879 : (x (-2) 1).toNat = 0 := by
          have r21880 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21881 := hb (x (-2) 1)
          have b21882 := hb (x (-1) 14)
          clear * - r21880 b21881 b21882 d21875
          omega
        have d21883 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
          have r21884 := hand1 (x (-2) 1) (x (-2) 14)
          have b21885 := hb (x (-2) 1)
          have b21886 := hb (x (-2) 1 && x (-2) 14)
          clear * - r21884 b21885 b21886 d21879
          omega
        have d21887 : (x (-3) 2).toNat = 1 := by
          have r21888 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b21889 := hb (x (-3) 2)
          have b21890 := hb (x (-1) 13)
          have b21891 := hb (x (-2) 1 && x (-2) 14)
          clear * - r21888 b21889 b21890 b21891 d21850 d21883
          omega
        have d21892 : (x (-2) 13).toNat = 0 := by
          have r21893 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
          have b21894 := hb (x (-2) 1)
          have b21895 := hb (x (-2) 13)
          clear * - r21893 b21894 b21895 d21879
          omega
        have d21896 : (x (-3) 3).toNat = 0 := by
          have r21897 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21898 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e21899 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b21900 := hb (x (-3) 3)
          have b21901 := hb (x (-2) 2)
          have b21902 := hb (x (-1) 13)
          have b21903 := hb (x 0 12)
          clear * - r21897 e21898 e21899 b21900 b21901 b21902 b21903 f21849 d21850 d21858
          omega
        have d21904 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
          have r21905 := hand1 (x (-3) 3) (x (-3) 14)
          have b21906 := hb (x (-3) 3)
          have b21907 := hb (x (-3) 3 && x (-3) 14)
          clear * - r21905 b21906 b21907 d21896
          omega
        have d21908 : (x (-1) 12).toNat = 0 := by
          have r21909 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e21910 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e21911 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b21912 := hb (x (-4) 3)
          have b21913 := hb (x (-3) 2)
          have b21914 := hb (x (-2) 13)
          have b21915 := hb (x (-1) 12)
          clear * - r21909 e21910 e21911 b21912 b21913 b21914 b21915 d21892 d21887
          omega
        have d21916 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
          have r21917 := hand2 (x (-1) 1) (x (-1) 12)
          have b21918 := hb (x (-1) 12)
          have b21919 := hb (x (-1) 1 && x (-1) 12)
          clear * - r21917 b21918 b21919 d21908
          omega
        have r21920 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21921 := hb (x (-4) 4)
        have b21922 := hb (x 0 11)
        have b21923 := hb (x (-1) 1 && x (-1) 12)
        have b21924 := hb (x (-2) 2 && x (-2) 13)
        have b21925 := hb (x (-3) 3 && x (-3) 14)
        linarith only [r21920, b21921, b21922, b21923, b21924, b21925, d19484, d21916, d21866, d21904, d19313]
    · have f21926 : (x 0 4).toNat = 1 := by rw [h19746]; rfl
      have d21927 : (x 0 12).toNat = 1 := by
        have r21928 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
        have b21929 := hb (x 0 4)
        have b21930 := hb (x 0 12)
        clear * - r21928 b21929 b21930 f21926
        omega
      have d21931 : (x (-1) 13).toNat = 0 := by
        have r21932 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21933 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e21934 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b21935 := hb (x (-3) 3)
        have b21936 := hb (x (-2) 2)
        have b21937 := hb (x (-1) 13)
        have b21938 := hb (x 0 12)
        clear * - r21932 e21933 e21934 b21935 b21936 b21937 b21938 d21927
        omega
      have d21939 : (x (-2) 2).toNat = 0 := by
        have r21940 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21941 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e21942 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b21943 := hb (x (-3) 3)
        have b21944 := hb (x (-2) 2)
        have b21945 := hb (x (-1) 13)
        have b21946 := hb (x 0 12)
        clear * - r21940 e21941 e21942 b21943 b21944 b21945 b21946 d21927 d21931
        omega
      have d21947 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
        have r21948 := hand1 (x (-2) 2) (x (-2) 13)
        have b21949 := hb (x (-2) 2)
        have b21950 := hb (x (-2) 2 && x (-2) 13)
        clear * - r21948 b21949 b21950 d21939
        omega
      have d21951 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
        have r21952 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21953 := hb (x (-2) 2)
        have b21954 := hb (x 0 13)
        have b21955 := hb (x (-1) 1 && x (-1) 14)
        clear * - r21952 b21953 b21954 b21955 g3 d21939
        omega
      have d21956 : (x (-1) 14).toNat = 1 := by
        have r21957 := hand2 (x (-1) 1) (x (-1) 14)
        have b21958 := hb (x (-1) 14)
        have b21959 := hb (x (-1) 1 && x (-1) 14)
        clear * - r21957 b21958 b21959 d21951
        omega
      have d21960 : (x (-2) 1).toNat = 0 := by
        have r21961 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21962 := hb (x (-2) 1)
        have b21963 := hb (x (-1) 14)
        clear * - r21961 b21962 b21963 d21956
        omega
      have d21964 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
        have r21965 := hand1 (x (-2) 1) (x (-2) 14)
        have b21966 := hb (x (-2) 1)
        have b21967 := hb (x (-2) 1 && x (-2) 14)
        clear * - r21965 b21966 b21967 d21960
        omega
      have d21968 : (x (-3) 2).toNat = 1 := by
        have r21969 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21970 := hb (x (-3) 2)
        have b21971 := hb (x (-1) 13)
        have b21972 := hb (x (-2) 1 && x (-2) 14)
        clear * - r21969 b21970 b21971 b21972 d21931 d21964
        omega
      have d21973 : (x (-2) 13).toNat = 0 := by
        have r21974 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
        have b21975 := hb (x (-2) 1)
        have b21976 := hb (x (-2) 13)
        clear * - r21974 b21975 b21976 d21960
        omega
      have d21977 : (x (-3) 3).toNat = 0 := by
        have r21978 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21979 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e21980 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b21981 := hb (x (-3) 3)
        have b21982 := hb (x (-2) 2)
        have b21983 := hb (x (-1) 13)
        have b21984 := hb (x 0 12)
        clear * - r21978 e21979 e21980 b21981 b21982 b21983 b21984 d21927 d21931 d21939
        omega
      have d21985 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
        have r21986 := hand1 (x (-3) 3) (x (-3) 14)
        have b21987 := hb (x (-3) 3)
        have b21988 := hb (x (-3) 3 && x (-3) 14)
        clear * - r21986 b21987 b21988 d21977
        omega
      have d21989 : (x (-1) 12).toNat = 0 := by
        have r21990 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21991 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e21992 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b21993 := hb (x (-4) 3)
        have b21994 := hb (x (-3) 2)
        have b21995 := hb (x (-2) 13)
        have b21996 := hb (x (-1) 12)
        clear * - r21990 e21991 e21992 b21993 b21994 b21995 b21996 d21973 d21968
        omega
      have d21997 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
        have r21998 := hand2 (x (-1) 1) (x (-1) 12)
        have b21999 := hb (x (-1) 12)
        have b22000 := hb (x (-1) 1 && x (-1) 12)
        clear * - r21998 b21999 b22000 d21989
        omega
      have r22001 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22002 := hb (x (-4) 4)
      have b22003 := hb (x 0 11)
      have b22004 := hb (x (-1) 1 && x (-1) 12)
      have b22005 := hb (x (-2) 2 && x (-2) 13)
      have b22006 := hb (x (-3) 3 && x (-3) 14)
      linarith only [r22001, b22002, b22003, b22004, b22005, b22006, d19484, d21997, d21947, d21985, d19313]
  · have f22007 : (x 0 2).toNat = 1 := by rw [h19413]; rfl
    have d22008 : (x 0 14).toNat = 1 := by
      have r22009 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
      have b22010 := hb (x 0 2)
      have b22011 := hb (x 0 14)
      clear * - r22009 b22010 b22011 f22007
      omega
    have d22012 : (x (-1) 1).toNat = 0 := by
      have r22013 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22014 := hb (x (-1) 1)
      have b22015 := hb (x 0 14)
      clear * - r22013 b22014 b22015 d22008
      omega
    have d22016 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
      have r22017 := hand1 (x (-1) 1) (x (-1) 14)
      have b22018 := hb (x (-1) 1)
      have b22019 := hb (x (-1) 1 && x (-1) 14)
      clear * - r22017 b22018 b22019 d22012
      omega
    have d22020 : (x (-1) 13).toNat = 0 := by
      have r22021 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
      have b22022 := hb (x (-1) 1)
      have b22023 := hb (x (-1) 13)
      clear * - r22021 b22022 b22023 d22012
      omega
    have d22024 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
      have r22025 := hand2 (x (-1) 3) (x (-1) 13)
      have b22026 := hb (x (-1) 13)
      have b22027 := hb (x (-1) 3 && x (-1) 13)
      clear * - r22025 b22026 b22027 d22020
      omega
    have d22028 : (x (-1) 5).toNat = 0 := by
      have r22029 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
      have b22030 := hb (x (-1) 5)
      have b22031 := hb (x (-1) 13)
      clear * - r22029 b22030 b22031 d22020
      omega
    have d22032 : (x (-2) 2).toNat = 1 := by
      have r22033 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22034 := hb (x (-2) 2)
      have b22035 := hb (x 0 13)
      have b22036 := hb (x (-1) 1 && x (-1) 14)
      clear * - r22033 b22034 b22035 b22036 g3 d22016
      omega
    have d22037 : (x (-2) 14).toNat = 1 := by
      have r22038 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
      have b22039 := hb (x (-2) 2)
      have b22040 := hb (x (-2) 14)
      clear * - r22038 b22039 b22040 d22032
      omega
    have d22041 : (x (-3) 1).toNat = 0 := by
      have r22042 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22043 := hb (x (-3) 1)
      have b22044 := hb (x (-2) 14)
      clear * - r22042 b22043 b22044 d22037
      omega
    have d22045 : (x (-3) 13).toNat = 0 := by
      have r22046 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
      have b22047 := hb (x (-3) 1)
      have b22048 := hb (x (-3) 13)
      clear * - r22046 b22047 b22048 d22041
      omega
    have d22049 : (x (-3) 9 && x (-3) 13).toNat = 0 := by
      have r22050 := hand2 (x (-3) 9) (x (-3) 13)
      have b22051 := hb (x (-3) 13)
      have b22052 := hb (x (-3) 9 && x (-3) 13)
      clear * - r22050 b22051 b22052 d22045
      omega
    have d22053 : (x (-3) 5).toNat = 0 := by
      have r22054 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
      have b22055 := hb (x (-3) 5)
      have b22056 := hb (x (-3) 13)
      clear * - r22054 b22055 b22056 d22045
      omega
    have d22057 : (x (-3) 9).toNat = 0 := by
      have r22058 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
      have b22059 := hb (x (-3) 1)
      have b22060 := hb (x (-3) 9)
      clear * - r22058 b22059 b22060 d22041
      omega
    have d22061 : (x 2 12).toNat = 0 := by
      have r22062 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22063 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e22064 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b22065 := hb (x (-1) 3)
      have b22066 := hb (x 0 2)
      have b22067 := hb (x 1 13)
      have b22068 := hb (x 2 12)
      clear * - r22062 e22063 e22064 b22065 b22066 b22067 b22068 f22007
      omega
    have d22069 : (x 2 2 && x 2 12).toNat = 0 := by
      have r22070 := hand2 (x 2 2) (x 2 12)
      have b22071 := hb (x 2 12)
      have b22072 := hb (x 2 2 && x 2 12)
      clear * - r22070 b22071 b22072 d22061
      omega
    have d22073 : (x 2 4).toNat = 0 := by
      have r22074 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
      have b22075 := hb (x 2 4)
      have b22076 := hb (x 2 12)
      clear * - r22074 b22075 b22076 d22061
      omega
    have d22077 : (x 2 4 && x 2 13).toNat = 0 := by
      have r22078 := hand1 (x 2 4) (x 2 13)
      have b22079 := hb (x 2 4)
      have b22080 := hb (x 2 4 && x 2 13)
      clear * - r22078 b22079 b22080 d22073
      omega
    have d22081 : (x 2 4 && x 2 8).toNat = 0 := by
      have r22082 := hand1 (x 2 4) (x 2 8)
      have b22083 := hb (x 2 4)
      have b22084 := hb (x 2 4 && x 2 8)
      clear * - r22082 b22083 b22084 d22073
      omega
    have d22085 : (x 1 13).toNat = 0 := by
      have r22086 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22087 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e22088 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b22089 := hb (x (-1) 3)
      have b22090 := hb (x 0 2)
      have b22091 := hb (x 1 13)
      have b22092 := hb (x 2 12)
      clear * - r22086 e22087 e22088 b22089 b22090 b22091 b22092 d22061 f22007
      omega
    have d22093 : (x 1 3 && x 1 13).toNat = 0 := by
      have r22094 := hand2 (x 1 3) (x 1 13)
      have b22095 := hb (x 1 13)
      have b22096 := hb (x 1 3 && x 1 13)
      clear * - r22094 b22095 b22096 d22085
      omega
    have d22097 : (x 1 5).toNat = 0 := by
      have r22098 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
      have b22099 := hb (x 1 5)
      have b22100 := hb (x 1 13)
      clear * - r22098 b22099 b22100 d22085
      omega
    have d22101 : (x 1 5 && x 1 9).toNat = 0 := by
      have r22102 := hand1 (x 1 5) (x 1 9)
      have b22103 := hb (x 1 5)
      have b22104 := hb (x 1 5 && x 1 9)
      clear * - r22102 b22103 b22104 d22097
      omega
    have d22105 : (x (-1) 3).toNat = 0 := by
      have r22106 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22107 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e22108 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b22109 := hb (x (-1) 3)
      have b22110 := hb (x 0 2)
      have b22111 := hb (x 1 13)
      have b22112 := hb (x 2 12)
      clear * - r22106 e22107 e22108 b22109 b22110 b22111 b22112 d22061 d22085 f22007
      omega
    have d22113 : (x (-1) 11).toNat = 0 := by
      have r22114 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b22115 := hb (x (-1) 3)
      have b22116 := hb (x (-1) 11)
      clear * - r22114 b22115 b22116 d22105
      omega
    have d22117 : (x (-1) 7 && x (-1) 11).toNat = 0 := by
      have r22118 := hand2 (x (-1) 7) (x (-1) 11)
      have b22119 := hb (x (-1) 11)
      have b22120 := hb (x (-1) 7 && x (-1) 11)
      clear * - r22118 b22119 b22120 d22113
      omega
    have d22121 : (x 0 12).toNat = 0 := by
      have r22122 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22123 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e22124 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b22125 := hb (x (-3) 3)
      have b22126 := hb (x (-2) 2)
      have b22127 := hb (x (-1) 13)
      have b22128 := hb (x 0 12)
      clear * - r22122 e22123 e22124 b22125 b22126 b22127 b22128 d22020 d22032
      omega
    have d22129 : (x 0 2 && x 0 12).toNat = 0 := by
      have r22130 := hand2 (x 0 2) (x 0 12)
      have b22131 := hb (x 0 12)
      have b22132 := hb (x 0 2 && x 0 12)
      clear * - r22130 b22131 b22132 d22121
      omega
    have d22133 : (x 0 4).toNat = 0 := by
      have r22134 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
      have b22135 := hb (x 0 4)
      have b22136 := hb (x 0 12)
      clear * - r22134 b22135 b22136 d22121
      omega
    have d22137 : (x 0 4 && x 0 14).toNat = 0 := by
      have r22138 := hand1 (x 0 4) (x 0 14)
      have b22139 := hb (x 0 4)
      have b22140 := hb (x 0 4 && x 0 14)
      clear * - r22138 b22139 b22140 d22133
      omega
    have d22141 : (x 3 3 && x 3 12).toNat = 1 := by
      have r22142 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22143 := hb (x 0 6)
      have b22144 := hb (x 6 9)
      have b22145 := hb (x 5 1 && x 5 10)
      have b22146 := hb (x 4 2 && x 4 11)
      have b22147 := hb (x 3 3 && x 3 12)
      have b22148 := hb (x 2 4 && x 2 13)
      have b22149 := hb (x 1 5 && x 1 14)
      clear * - r22142 b22143 b22144 b22145 b22146 b22147 b22148 b22149 g11 g19 g20 d22077 g21 g1
      omega
    have d22150 : (x 3 12).toNat = 1 := by
      have r22151 := hand2 (x 3 3) (x 3 12)
      have b22152 := hb (x 3 12)
      have b22153 := hb (x 3 3 && x 3 12)
      clear * - r22151 b22152 b22153 d22141
      omega
    have d22154 : (x 2 13).toNat = 0 := by
      have r22155 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22156 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e22157 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b22158 := hb (x 0 3)
      have b22159 := hb (x 1 2)
      have b22160 := hb (x 2 13)
      have b22161 := hb (x 3 12)
      clear * - r22155 e22156 e22157 b22158 b22159 b22160 b22161 d22150 g4
      omega
    have d22162 : (x 2 2 && x 2 13).toNat = 0 := by
      have r22163 := hand2 (x 2 2) (x 2 13)
      have b22164 := hb (x 2 13)
      have b22165 := hb (x 2 2 && x 2 13)
      clear * - r22163 b22164 b22165 d22154
      omega
    have d22166 : (x 3 1 && x 3 12).toNat = 1 := by
      have r22167 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22168 := hb (x 0 4)
      have b22169 := hb (x 4 11)
      have b22170 := hb (x 3 1 && x 3 12)
      have b22171 := hb (x 2 2 && x 2 13)
      have b22172 := hb (x 1 3 && x 1 14)
      clear * - r22167 b22168 b22169 b22170 b22171 b22172 g9 d22162 g29 d22133
      omega
    have d22173 : (x 3 1).toNat = 1 := by
      have r22174 := hand1 (x 3 1) (x 3 12)
      have b22175 := hb (x 3 1)
      have b22176 := hb (x 3 1 && x 3 12)
      clear * - r22174 b22175 b22176 d22166
      omega
    have d22177 : (x 4 14).toNat = 0 := by
      have r22178 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22179 := hb (x 3 1)
      have b22180 := hb (x 4 14)
      clear * - r22178 b22179 b22180 d22173
      omega
    have d22181 : (x 4 1 && x 4 14).toNat = 0 := by
      have r22182 := hand2 (x 4 1) (x 4 14)
      have b22183 := hb (x 4 14)
      have b22184 := hb (x 4 1 && x 4 14)
      clear * - r22182 b22183 b22184 d22177
      omega
    have d22185 : (x 4 3 && x 4 14).toNat = 0 := by
      have r22186 := hand2 (x 4 3) (x 4 14)
      have b22187 := hb (x 4 14)
      have b22188 := hb (x 4 3 && x 4 14)
      clear * - r22186 b22187 b22188 d22177
      omega
    have d22189 : (x 4 6).toNat = 0 := by
      have r22190 : (x 4 6).toNat ≤ (x 4 14).toNat := himp _ _ (hp6 4)
      have b22191 := hb (x 4 6)
      have b22192 := hb (x 4 14)
      clear * - r22190 b22191 b22192 d22177
      omega
    have d22193 : (x 4 2 && x 4 6).toNat = 0 := by
      have r22194 := hand2 (x 4 2) (x 4 6)
      have b22195 := hb (x 4 6)
      have b22196 := hb (x 4 2 && x 4 6)
      clear * - r22194 b22195 b22196 d22189
      omega
    have d22197 : (x 4 2).toNat = 0 := by
      have r22198 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
      have b22199 := hb (x 4 2)
      have b22200 := hb (x 4 14)
      clear * - r22198 b22199 b22200 d22177
      omega
    have d22201 : (x 4 10).toNat = 0 := by
      have r22202 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
      have b22203 := hb (x 4 2)
      have b22204 := hb (x 4 10)
      clear * - r22202 b22203 b22204 d22197
      omega
    have d22205 : (x 3 1 && x 3 11).toNat = 1 := by
      have r22206 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22207 := hb (x (-1) 5)
      have b22208 := hb (x 4 10)
      have b22209 := hb (x 3 1 && x 3 11)
      have b22210 := hb (x 2 2 && x 2 12)
      have b22211 := hb (x 1 3 && x 1 13)
      have b22212 := hb (x 0 4 && x 0 14)
      clear * - r22206 b22207 b22208 b22209 b22210 b22211 b22212 d22201 d22069 d22093 d22137 d22028
      omega
    have d22213 : (x 3 11).toNat = 1 := by
      have r22214 := hand2 (x 3 1) (x 3 11)
      have b22215 := hb (x 3 11)
      have b22216 := hb (x 3 1 && x 3 11)
      clear * - r22214 b22215 b22216 d22205
      omega
    have d22217 : (x 3 3).toNat = 1 := by
      have r22218 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b22219 := hb (x 3 3)
      have b22220 := hb (x 3 11)
      clear * - r22218 b22219 b22220 d22213
      omega
    have d22221 : (x 6 12).toNat = 0 := by
      have r22222 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22223 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e22224 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b22225 := hb (x 3 3)
      have b22226 := hb (x 4 2)
      have b22227 := hb (x 5 13)
      have b22228 := hb (x 6 12)
      clear * - r22222 e22223 e22224 b22225 b22226 b22227 b22228 d22197 d22217
      omega
    have d22229 : (x 6 1 && x 6 12).toNat = 0 := by
      have r22230 := hand2 (x 6 1) (x 6 12)
      have b22231 := hb (x 6 12)
      have b22232 := hb (x 6 1 && x 6 12)
      clear * - r22230 b22231 b22232 d22221
      omega
    have d22233 : (x 6 4).toNat = 0 := by
      have r22234 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
      have b22235 := hb (x 6 4)
      have b22236 := hb (x 6 12)
      clear * - r22234 b22235 b22236 d22221
      omega
    have d22237 : (x 5 13).toNat = 0 := by
      have r22238 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22239 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e22240 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b22241 := hb (x 3 3)
      have b22242 := hb (x 4 2)
      have b22243 := hb (x 5 13)
      have b22244 := hb (x 6 12)
      clear * - r22238 e22239 e22240 b22241 b22242 b22243 b22244 d22221 d22197 d22217
      omega
    have d22245 : (x 5 2 && x 5 13).toNat = 0 := by
      have r22246 := hand2 (x 5 2) (x 5 13)
      have b22247 := hb (x 5 13)
      have b22248 := hb (x 5 2 && x 5 13)
      clear * - r22246 b22247 b22248 d22237
      omega
    have d22249 : (x 7 11).toNat = 1 := by
      have r22250 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22251 := hb (x 3 4)
      have b22252 := hb (x 7 11)
      have b22253 := hb (x 6 1 && x 6 12)
      have b22254 := hb (x 5 2 && x 5 13)
      have b22255 := hb (x 4 3 && x 4 14)
      clear * - r22250 b22251 b22252 b22253 b22254 b22255 d22229 d22245 d22185 g8
      omega
    have d22256 : (x 7 3).toNat = 1 := by
      have r22257 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
      have b22258 := hb (x 7 3)
      have b22259 := hb (x 7 11)
      clear * - r22257 b22258 b22259 d22249
      omega
    have d22260 : (x 10 12).toNat = 0 := by
      have r22261 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22262 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e22263 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b22264 := hb (x 7 3)
      have b22265 := hb (x 8 2)
      have b22266 := hb (x 9 13)
      have b22267 := hb (x 10 12)
      clear * - r22261 e22262 e22263 b22264 b22265 b22266 b22267 d22256
      omega
    have d22268 : (x 9 13).toNat = 0 := by
      have r22269 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22270 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e22271 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b22272 := hb (x 7 3)
      have b22273 := hb (x 8 2)
      have b22274 := hb (x 9 13)
      have b22275 := hb (x 10 12)
      clear * - r22269 e22270 e22271 b22272 b22273 b22274 b22275 d22260 d22256
      omega
    have d22276 : (x 8 2).toNat = 0 := by
      have r22277 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22278 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e22279 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b22280 := hb (x 7 3)
      have b22281 := hb (x 8 2)
      have b22282 := hb (x 9 13)
      have b22283 := hb (x 10 12)
      clear * - r22277 e22278 e22279 b22280 b22281 b22282 b22283 d22260 d22268 d22256
      omega
    have d22284 : (x 8 10).toNat = 0 := by
      have r22285 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
      have b22286 := hb (x 8 2)
      have b22287 := hb (x 8 10)
      clear * - r22285 b22286 b22287 d22276
      omega
    have d22288 : (x 5 5).toNat = 0 := by
      have r22289 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
      have b22290 := hb (x 5 5)
      have b22291 := hb (x 5 13)
      clear * - r22289 b22290 b22291 d22237
      omega
    have d22292 : (x 3 2).toNat = 1 := by
      have r22293 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22294 := hb (x 3 2)
      have b22295 := hb (x 5 13)
      have b22296 := hb (x 4 1 && x 4 14)
      clear * - r22293 b22294 b22295 b22296 d22237 d22181
      omega
    have d22297 : (x 3 14).toNat = 1 := by
      have r22298 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b22299 := hb (x 3 2)
      have b22300 := hb (x 3 14)
      clear * - r22298 b22299 b22300 d22292
      omega
    have d22301 : (x 2 1).toNat = 0 := by
      have r22302 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22303 := hb (x 2 1)
      have b22304 := hb (x 3 14)
      clear * - r22302 b22303 b22304 d22297
      omega
    have d22305 : (x 2 1 && x 2 14).toNat = 0 := by
      have r22306 := hand1 (x 2 1) (x 2 14)
      have b22307 := hb (x 2 1)
      have b22308 := hb (x 2 1 && x 2 14)
      clear * - r22306 b22307 b22308 d22301
      omega
    have d22309 : (x 3 13).toNat = 1 := by
      have r22310 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22311 := hb (x 1 2)
      have b22312 := hb (x 3 13)
      have b22313 := hb (x 2 1 && x 2 14)
      clear * - r22310 b22311 b22312 b22313 d22305 g4
      omega
    have d22314 : (x 4 12).toNat = 0 := by
      have r22315 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22316 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e22317 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b22318 := hb (x 1 3)
      have b22319 := hb (x 2 2)
      have b22320 := hb (x 3 13)
      have b22321 := hb (x 4 12)
      clear * - r22315 e22316 e22317 b22318 b22319 b22320 b22321 d22309
      omega
    have d22322 : (x 2 2).toNat = 0 := by
      have r22323 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22324 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e22325 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b22326 := hb (x 1 3)
      have b22327 := hb (x 2 2)
      have b22328 := hb (x 3 13)
      have b22329 := hb (x 4 12)
      clear * - r22323 e22324 e22325 b22326 b22327 b22328 b22329 d22314 d22309
      omega
    have d22330 : (x 2 10).toNat = 0 := by
      have r22331 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
      have b22332 := hb (x 2 2)
      have b22333 := hb (x 2 10)
      clear * - r22331 b22332 b22333 d22322
      omega
    have d22334 : (x 1 3).toNat = 0 := by
      have r22335 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22336 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e22337 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b22338 := hb (x 1 3)
      have b22339 := hb (x 2 2)
      have b22340 := hb (x 3 13)
      have b22341 := hb (x 4 12)
      clear * - r22335 e22336 e22337 b22338 b22339 b22340 b22341 d22314 d22309 d22322
      omega
    have d22342 : (x 1 11).toNat = 0 := by
      have r22343 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
      have b22344 := hb (x 1 3)
      have b22345 := hb (x 1 11)
      clear * - r22343 b22344 b22345 d22334
      omega
    have d22346 : (x 1 1 && x 1 11).toNat = 0 := by
      have r22347 := hand2 (x 1 1) (x 1 11)
      have b22348 := hb (x 1 11)
      have b22349 := hb (x 1 1 && x 1 11)
      clear * - r22347 b22348 b22349 d22342
      omega
    have d22350 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
      have r22351 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22352 := hb (x (-3) 5)
      have b22353 := hb (x 2 10)
      have b22354 := hb (x 1 1 && x 1 11)
      have b22355 := hb (x 0 2 && x 0 12)
      have b22356 := hb (x (-1) 3 && x (-1) 13)
      have b22357 := hb (x (-2) 4 && x (-2) 14)
      clear * - r22351 b22352 b22353 b22354 b22355 b22356 b22357 d22330 d22346 d22129 d22024 d22053
      omega
    have d22358 : (x (-2) 4).toNat = 1 := by
      have r22359 := hand1 (x (-2) 4) (x (-2) 14)
      have b22360 := hb (x (-2) 4)
      have b22361 := hb (x (-2) 4 && x (-2) 14)
      clear * - r22359 b22360 b22361 d22350
      omega
    have d22362 : (x (-2) 12).toNat = 1 := by
      have r22363 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
      have b22364 := hb (x (-2) 4)
      have b22365 := hb (x (-2) 12)
      clear * - r22363 b22364 b22365 d22358
      omega
    have d22366 : (x (-4) 2).toNat = 0 := by
      have r22367 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22368 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e22369 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b22370 := hb (x (-5) 3)
      have b22371 := hb (x (-4) 2)
      have b22372 := hb (x (-3) 13)
      have b22373 := hb (x (-2) 12)
      clear * - r22367 e22368 e22369 b22370 b22371 b22372 b22373 d22362 d22045
      omega
    have d22374 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
      have r22375 := hand1 (x (-4) 2) (x (-4) 12)
      have b22376 := hb (x (-4) 2)
      have b22377 := hb (x (-4) 2 && x (-4) 12)
      clear * - r22375 b22376 b22377 d22366
      omega
    have d22378 : (x (-4) 10).toNat = 0 := by
      have r22379 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
      have b22380 := hb (x (-4) 2)
      have b22381 := hb (x (-4) 10)
      clear * - r22379 b22380 b22381 d22366
      omega
    have d22382 : (x (-5) 3).toNat = 0 := by
      have r22383 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22384 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e22385 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have b22386 := hb (x (-5) 3)
      have b22387 := hb (x (-4) 2)
      have b22388 := hb (x (-3) 13)
      have b22389 := hb (x (-2) 12)
      clear * - r22383 e22384 e22385 b22386 b22387 b22388 b22389 d22362 d22045 d22366
      omega
    have d22390 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
      have r22391 := hand1 (x (-5) 3) (x (-5) 13)
      have b22392 := hb (x (-5) 3)
      have b22393 := hb (x (-5) 3 && x (-5) 13)
      clear * - r22391 b22392 b22393 d22382
      omega
    have d22394 : (x (-5) 11).toNat = 0 := by
      have r22395 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
      have b22396 := hb (x (-5) 3)
      have b22397 := hb (x (-5) 11)
      clear * - r22395 b22396 b22397 d22382
      omega
    have d22398 : (x 10 8).toNat = 0 := by
      have r22399 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22400 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e22401 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e22402 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e22403 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e22404 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e22405 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b22406 := hb (x 3 7)
      have b22407 := hb (x 4 6)
      have b22408 := hb (x 5 5)
      have b22409 := hb (x 6 4)
      have b22410 := hb (x 7 11)
      have b22411 := hb (x 8 10)
      have b22412 := hb (x 9 9)
      have b22413 := hb (x 10 8)
      clear * - r22399 e22400 e22401 e22402 e22403 e22404 e22405 b22406 b22407 b22408 b22409 b22410 b22411 b22412 b22413 d22284 d22249 d22233 d22288 d22189
      omega
    have d22414 : (x 9 9).toNat = 0 := by
      have r22415 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22416 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e22417 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e22418 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e22419 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e22420 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e22421 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b22422 := hb (x 3 7)
      have b22423 := hb (x 4 6)
      have b22424 := hb (x 5 5)
      have b22425 := hb (x 6 4)
      have b22426 := hb (x 7 11)
      have b22427 := hb (x 8 10)
      have b22428 := hb (x 9 9)
      have b22429 := hb (x 10 8)
      clear * - r22415 e22416 e22417 e22418 e22419 e22420 e22421 b22422 b22423 b22424 b22425 b22426 b22427 b22428 b22429 d22398 d22284 d22249 d22233 d22288 d22189
      omega
    have d22430 : (x 3 7).toNat = 0 := by
      have r22431 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22432 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e22433 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e22434 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e22435 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e22436 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e22437 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b22438 := hb (x 3 7)
      have b22439 := hb (x 4 6)
      have b22440 := hb (x 5 5)
      have b22441 := hb (x 6 4)
      have b22442 := hb (x 7 11)
      have b22443 := hb (x 8 10)
      have b22444 := hb (x 9 9)
      have b22445 := hb (x 10 8)
      clear * - r22431 e22432 e22433 e22434 e22435 e22436 e22437 b22438 b22439 b22440 b22441 b22442 b22443 b22444 b22445 d22398 d22414 d22284 d22249 d22233 d22288 d22189
      omega
    have d22446 : (x 3 3 && x 3 7).toNat = 0 := by
      have r22447 := hand2 (x 3 3) (x 3 7)
      have b22448 := hb (x 3 7)
      have b22449 := hb (x 3 3 && x 3 7)
      clear * - r22447 b22448 b22449 d22430
      omega
    have d22450 : (x (-2) 8 && x (-2) 12).toNat = 1 := by
      have r22451 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22452 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
      have e22453 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
      have b22454 := hb (x (-5) 11)
      have b22455 := hb (x (-4) 10)
      have b22456 := hb (x 5 5)
      have b22457 := hb (x 6 4)
      have b22458 := hb (x 4 2 && x 4 6)
      have b22459 := hb (x 3 3 && x 3 7)
      have b22460 := hb (x 2 4 && x 2 8)
      have b22461 := hb (x 1 5 && x 1 9)
      have b22462 := hb (x 0 6 && x 0 10)
      have b22463 := hb (x (-1) 7 && x (-1) 11)
      have b22464 := hb (x (-2) 8 && x (-2) 12)
      have b22465 := hb (x (-3) 9 && x (-3) 13)
      clear * - r22451 e22452 e22453 b22454 b22455 b22456 b22457 b22458 b22459 b22460 b22461 b22462 b22463 b22464 b22465 d22233 d22288 d22193 d22446 d22081 d22101 g13 d22117 d22049 d22378 d22394
      omega
    have d22466 : (x (-2) 8).toNat = 1 := by
      have r22467 := hand1 (x (-2) 8) (x (-2) 12)
      have b22468 := hb (x (-2) 8)
      have b22469 := hb (x (-2) 8 && x (-2) 12)
      clear * - r22467 b22468 b22469 d22450
      omega
    have d22470 : (x (-6) 4).toNat = 0 := by
      have r22471 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22472 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
      have e22473 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
      have e22474 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
      have e22475 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
      have e22476 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
      have e22477 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
      have b22478 := hb (x (-9) 7)
      have b22479 := hb (x (-8) 6)
      have b22480 := hb (x (-7) 5)
      have b22481 := hb (x (-6) 4)
      have b22482 := hb (x (-5) 11)
      have b22483 := hb (x (-4) 10)
      have b22484 := hb (x (-3) 9)
      have b22485 := hb (x (-2) 8)
      clear * - r22471 e22472 e22473 e22474 e22475 e22476 e22477 b22478 b22479 b22480 b22481 b22482 b22483 b22484 b22485 d22466 d22057 d22378 d22394
      omega
    have d22486 : (x (-6) 4 && x (-6) 14).toNat = 0 := by
      have r22487 := hand1 (x (-6) 4) (x (-6) 14)
      have b22488 := hb (x (-6) 4)
      have b22489 := hb (x (-6) 4 && x (-6) 14)
      clear * - r22487 b22488 b22489 d22470
      omega
    have d22490 : (x (-7) 5).toNat = 1 := by
      have r22491 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22492 := hb (x (-7) 5)
      have b22493 := hb (x (-2) 10)
      have b22494 := hb (x (-3) 1 && x (-3) 11)
      have b22495 := hb (x (-4) 2 && x (-4) 12)
      have b22496 := hb (x (-5) 3 && x (-5) 13)
      have b22497 := hb (x (-6) 4 && x (-6) 14)
      clear * - r22491 b22492 b22493 b22494 b22495 b22496 b22497 d19261 d19301 d22374 d22390 d22486
      omega
    have r22498 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22499 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e22500 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e22501 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e22502 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e22503 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e22504 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have b22505 := hb (x (-9) 7)
    have b22506 := hb (x (-8) 6)
    have b22507 := hb (x (-7) 5)
    have b22508 := hb (x (-6) 4)
    have b22509 := hb (x (-5) 11)
    have b22510 := hb (x (-4) 10)
    have b22511 := hb (x (-3) 9)
    have b22512 := hb (x (-2) 8)
    linarith only [r22498, e22499, e22500, e22501, e22502, e22503, e22504, b22505, b22506, b22507, b22508, b22509, b22510, b22511, b22512, d22466, d22057, d22378, d22394, d22470, d22490]

theorem cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b101 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 5).toNat = 0)
    (g1 : (x 0 6).toNat = 0)
    (g2 : (x 0 8).toNat = 1)
    (g3 : (x 0 13).toNat = 0)
    (g4 : (x 1 2).toNat = 0)
    (g5 : (x 1 6).toNat = 0)
    (g6 : (x 1 10).toNat = 0)
    (g7 : (x 2 5).toNat = 0)
    (g8 : (x 3 4).toNat = 0)
    (g9 : (x 4 11).toNat = 0)
    (g10 : (x 5 10).toNat = 0)
    (g11 : (x 6 9).toNat = 0)
    (g12 : (x 0 5 && x 0 9).toNat = 0)
    (g13 : (x 0 6 && x 0 10).toNat = 0)
    (g14 : (x 1 2 && x 1 7).toNat = 0)
    (g15 : (x 3 4 && x 3 11).toNat = 0)
    (g16 : (x 2 5 && x 2 12).toNat = 0)
    (g17 : (x 1 6 && x 1 13).toNat = 0)
    (g18 : (x 1 2 && x 1 11).toNat = 0)
    (g19 : (x 5 1 && x 5 10).toNat = 0)
    (g20 : (x 4 2 && x 4 11).toNat = 0)
    (g21 : (x 1 5 && x 1 14).toNat = 0)
    (g22 : (x 3 4 && x 3 13).toNat = 0)
    (g23 : (x 2 5 && x 2 14).toNat = 0)
    (g24 : (x 1 2 && x 1 12).toNat = 0)
    (g25 : (x 0 3 && x 0 13).toNat = 0)
    (g26 : (x 4 1 && x 4 11).toNat = 0)
    (g27 : (x 1 4 && x 1 14).toNat = 0)
    (g28 : (x 3 4 && x 3 14).toNat = 0)
    (g29 : (x 1 3 && x 1 14).toNat = 0)
    (g30 : (x 1 1 && x 1 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_six_iff_seven_core_b101_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30
