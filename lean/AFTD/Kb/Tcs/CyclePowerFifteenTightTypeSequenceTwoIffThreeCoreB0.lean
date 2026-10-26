import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_two_iff_three_core_b0

Topic: combinatorics   Node: cac1944bc226

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP; the same generator on the same window refutes x(0,2) != x(0,3) (a case-split tree of 109 + 3 nodes).

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_two_iff_three_core: under the layer-free tight-cover constraints for k = 15 and 8 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_b0_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 4).toNat = 0)
    (g1 : (x 3 4).toNat = 0)
    (g2 : (x 4 2).toNat = 0)
    (g3 : (x 4 4).toNat = 0)
    (g4 : (x 3 1 && x 3 12).toNat = 0)
    (g5 : (x 2 2 && x 2 13).toNat = 0)
    (g6 : (x 1 3 && x 1 14).toNat = 0)
    (g7 : (x 4 3 && x 4 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d201 : (x 4 11).toNat = 1 := by
    have r202 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b203 := hb (x 0 4)
    have b204 := hb (x 4 11)
    have b205 := hb (x 3 1 && x 3 12)
    have b206 := hb (x 2 2 && x 2 13)
    have b207 := hb (x 1 3 && x 1 14)
    clear * - r202 b203 b204 b205 b206 b207 g4 g5 g6 g0
    omega
  have d208 : (x 4 3).toNat = 1 := by
    have r209 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have b210 := hb (x 4 3)
    have b211 := hb (x 4 11)
    clear * - r209 b210 b211 d201
    omega
  have d212 : (x 7 12).toNat = 0 := by
    have r213 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e214 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e215 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b216 := hb (x 4 3)
    have b217 := hb (x 5 2)
    have b218 := hb (x 6 13)
    have b219 := hb (x 7 12)
    clear * - r213 e214 e215 b216 b217 b218 b219 d208
    omega
  have d220 : (x 7 1 && x 7 12).toNat = 0 := by
    have r221 := hand2 (x 7 1) (x 7 12)
    have b222 := hb (x 7 12)
    have b223 := hb (x 7 1 && x 7 12)
    clear * - r221 b222 b223 d212
    omega
  have d224 : (x 7 4).toNat = 0 := by
    have r225 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b226 := hb (x 7 4)
    have b227 := hb (x 7 12)
    clear * - r225 b226 b227 d212
    omega
  have d228 : (x 6 13).toNat = 0 := by
    have r229 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e230 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e231 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b232 := hb (x 4 3)
    have b233 := hb (x 5 2)
    have b234 := hb (x 6 13)
    have b235 := hb (x 7 12)
    clear * - r229 e230 e231 b232 b233 b234 b235 d212 d208
    omega
  have d236 : (x 6 2 && x 6 13).toNat = 0 := by
    have r237 := hand2 (x 6 2) (x 6 13)
    have b238 := hb (x 6 13)
    have b239 := hb (x 6 2 && x 6 13)
    clear * - r237 b238 b239 d228
    omega
  have d240 : (x 5 1 && x 5 14).toNat = 1 := by
    have r241 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b242 := hb (x 4 2)
    have b243 := hb (x 6 13)
    have b244 := hb (x 5 1 && x 5 14)
    clear * - r241 b242 b243 b244 d228 g2
    omega
  have d245 : (x 5 1).toNat = 1 := by
    have r246 := hand1 (x 5 1) (x 5 14)
    have b247 := hb (x 5 1)
    have b248 := hb (x 5 1 && x 5 14)
    clear * - r246 b247 b248 d240
    omega
  have d249 : (x 6 14).toNat = 0 := by
    have r250 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b251 := hb (x 5 1)
    have b252 := hb (x 6 14)
    clear * - r250 b251 b252 d245
    omega
  have d253 : (x 6 1 && x 6 14).toNat = 0 := by
    have r254 := hand2 (x 6 1) (x 6 14)
    have b255 := hb (x 6 14)
    have b256 := hb (x 6 1 && x 6 14)
    clear * - r254 b255 b256 d249
    omega
  have d257 : (x 6 2).toNat = 0 := by
    have r258 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
    have b259 := hb (x 6 2)
    have b260 := hb (x 6 14)
    clear * - r258 b259 b260 d249
    omega
  have d261 : (x 5 2).toNat = 0 := by
    have r262 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e263 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e264 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b265 := hb (x 4 3)
    have b266 := hb (x 5 2)
    have b267 := hb (x 6 13)
    have b268 := hb (x 7 12)
    clear * - r262 e263 e264 b265 b266 b267 b268 d212 d228 d208
    omega
  have d269 : (x 5 2 && x 5 13).toNat = 0 := by
    have r270 := hand1 (x 5 2) (x 5 13)
    have b271 := hb (x 5 2)
    have b272 := hb (x 5 2 && x 5 13)
    clear * - r270 b271 b272 d261
    omega
  have d273 : (x 7 13).toNat = 1 := by
    have r274 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b275 := hb (x 5 2)
    have b276 := hb (x 7 13)
    have b277 := hb (x 6 1 && x 6 14)
    clear * - r274 b275 b276 b277 d253 d261
    omega
  have d278 : (x 7 1).toNat = 1 := by
    have r279 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b280 := hb (x 7 1)
    have b281 := hb (x 7 13)
    clear * - r279 b280 b281 d273
    omega
  have d282 : (x 8 14).toNat = 0 := by
    have r283 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b284 := hb (x 7 1)
    have b285 := hb (x 8 14)
    clear * - r283 b284 b285 d278
    omega
  have d286 : (x 8 3 && x 8 14).toNat = 0 := by
    have r287 := hand2 (x 8 3) (x 8 14)
    have b288 := hb (x 8 14)
    have b289 := hb (x 8 3 && x 8 14)
    clear * - r287 b288 b289 d282
    omega
  have d290 : (x 8 2).toNat = 0 := by
    have r291 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
    have b292 := hb (x 8 2)
    have b293 := hb (x 8 14)
    clear * - r291 b292 b293 d282
    omega
  have d294 : (x 8 12).toNat = 0 := by
    have r295 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e296 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e297 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b298 := hb (x 5 3)
    have b299 := hb (x 6 2)
    have b300 := hb (x 7 13)
    have b301 := hb (x 8 12)
    clear * - r295 e296 e297 b298 b299 b300 b301 d273 d257
    omega
  have d302 : (x 8 4).toNat = 0 := by
    have r303 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
    have b304 := hb (x 8 4)
    have b305 := hb (x 8 12)
    clear * - r303 b304 b305 d294
    omega
  have d306 : (x 5 3).toNat = 0 := by
    have r307 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e308 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e309 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b310 := hb (x 5 3)
    have b311 := hb (x 6 2)
    have b312 := hb (x 7 13)
    have b313 := hb (x 8 12)
    clear * - r307 e308 e309 b310 b311 b312 b313 d294 d273 d257
    omega
  have d314 : (x 5 3 && x 5 14).toNat = 0 := by
    have r315 := hand1 (x 5 3) (x 5 14)
    have b316 := hb (x 5 3)
    have b317 := hb (x 5 3 && x 5 14)
    clear * - r315 b316 b317 d306
    omega
  have d318 : (x 8 11).toNat = 1 := by
    have r319 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b320 := hb (x 4 4)
    have b321 := hb (x 8 11)
    have b322 := hb (x 7 1 && x 7 12)
    have b323 := hb (x 6 2 && x 6 13)
    have b324 := hb (x 5 3 && x 5 14)
    clear * - r319 b320 b321 b322 b323 b324 d220 d236 d314 g3
    omega
  have d325 : (x 8 3).toNat = 1 := by
    have r326 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
    have b327 := hb (x 8 3)
    have b328 := hb (x 8 11)
    clear * - r326 b327 b328 d318
    omega
  have d329 : (x 11 12).toNat = 0 := by
    have r330 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e331 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e332 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b333 := hb (x 8 3)
    have b334 := hb (x 9 2)
    have b335 := hb (x 10 13)
    have b336 := hb (x 11 12)
    clear * - r330 e331 e332 b333 b334 b335 b336 d325
    omega
  have d337 : (x 11 1 && x 11 12).toNat = 0 := by
    have r338 := hand2 (x 11 1) (x 11 12)
    have b339 := hb (x 11 12)
    have b340 := hb (x 11 1 && x 11 12)
    clear * - r338 b339 b340 d329
    omega
  have d341 : (x 11 4).toNat = 0 := by
    have r342 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
    have b343 := hb (x 11 4)
    have b344 := hb (x 11 12)
    clear * - r342 b343 b344 d329
    omega
  have d345 : (x 10 13).toNat = 0 := by
    have r346 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e347 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e348 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b349 := hb (x 8 3)
    have b350 := hb (x 9 2)
    have b351 := hb (x 10 13)
    have b352 := hb (x 11 12)
    clear * - r346 e347 e348 b349 b350 b351 b352 d329 d325
    omega
  have d353 : (x 10 2 && x 10 13).toNat = 0 := by
    have r354 := hand2 (x 10 2) (x 10 13)
    have b355 := hb (x 10 13)
    have b356 := hb (x 10 2 && x 10 13)
    clear * - r354 b355 b356 d345
    omega
  have d357 : (x 9 1 && x 9 14).toNat = 1 := by
    have r358 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b359 := hb (x 8 2)
    have b360 := hb (x 10 13)
    have b361 := hb (x 9 1 && x 9 14)
    clear * - r358 b359 b360 b361 d345 d290
    omega
  have d362 : (x 9 14).toNat = 1 := by
    have r363 := hand2 (x 9 1) (x 9 14)
    have b364 := hb (x 9 14)
    have b365 := hb (x 9 1 && x 9 14)
    clear * - r363 b364 b365 d357
    omega
  have d366 : (x 8 1).toNat = 0 := by
    have r367 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b368 := hb (x 8 1)
    have b369 := hb (x 9 14)
    clear * - r367 b368 b369 d362
    omega
  have d370 : (x 8 13).toNat = 0 := by
    have r371 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b372 := hb (x 8 1)
    have b373 := hb (x 8 13)
    clear * - r371 b372 b373 d366
    omega
  have d374 : (x 7 1 && x 7 14).toNat = 1 := by
    have r375 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b376 := hb (x 6 2)
    have b377 := hb (x 8 13)
    have b378 := hb (x 7 1 && x 7 14)
    clear * - r375 b376 b377 b378 d370 d257
    omega
  have d379 : (x 7 14).toNat = 1 := by
    have r380 := hand2 (x 7 1) (x 7 14)
    have b381 := hb (x 7 14)
    have b382 := hb (x 7 1 && x 7 14)
    clear * - r380 b381 b382 d374
    omega
  have d383 : (x 6 1).toNat = 0 := by
    have r384 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b385 := hb (x 6 1)
    have b386 := hb (x 7 14)
    clear * - r384 b385 b386 d379
    omega
  have d387 : (x 6 1 && x 6 12).toNat = 0 := by
    have r388 := hand1 (x 6 1) (x 6 12)
    have b389 := hb (x 6 1)
    have b390 := hb (x 6 1 && x 6 12)
    clear * - r388 b389 b390 d383
    omega
  have d391 : (x 7 11).toNat = 1 := by
    have r392 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b393 := hb (x 3 4)
    have b394 := hb (x 7 11)
    have b395 := hb (x 6 1 && x 6 12)
    have b396 := hb (x 5 2 && x 5 13)
    have b397 := hb (x 4 3 && x 4 14)
    clear * - r392 b393 b394 b395 b396 b397 d387 d269 g7 g1
    omega
  have d398 : (x 7 3).toNat = 1 := by
    have r399 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b400 := hb (x 7 3)
    have b401 := hb (x 7 11)
    clear * - r399 b400 b401 d391
    omega
  have d402 : (x 10 12).toNat = 0 := by
    have r403 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e404 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e405 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b406 := hb (x 7 3)
    have b407 := hb (x 8 2)
    have b408 := hb (x 9 13)
    have b409 := hb (x 10 12)
    clear * - r403 e404 e405 b406 b407 b408 b409 d290 d398
    omega
  have d410 : (x 10 1 && x 10 12).toNat = 0 := by
    have r411 := hand2 (x 10 1) (x 10 12)
    have b412 := hb (x 10 12)
    have b413 := hb (x 10 1 && x 10 12)
    clear * - r411 b412 b413 d402
    omega
  have d414 : (x 9 13).toNat = 0 := by
    have r415 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e416 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e417 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b418 := hb (x 7 3)
    have b419 := hb (x 8 2)
    have b420 := hb (x 9 13)
    have b421 := hb (x 10 12)
    clear * - r415 e416 e417 b418 b419 b420 b421 d402 d290 d398
    omega
  have d422 : (x 9 2 && x 9 13).toNat = 0 := by
    have r423 := hand2 (x 9 2) (x 9 13)
    have b424 := hb (x 9 13)
    have b425 := hb (x 9 2 && x 9 13)
    clear * - r423 b424 b425 d414
    omega
  have d426 : (x 11 11).toNat = 1 := by
    have r427 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b428 := hb (x 7 4)
    have b429 := hb (x 11 11)
    have b430 := hb (x 10 1 && x 10 12)
    have b431 := hb (x 9 2 && x 9 13)
    have b432 := hb (x 8 3 && x 8 14)
    clear * - r427 b428 b429 b430 b431 b432 d410 d422 d286 d224
    omega
  have d433 : (x 11 3).toNat = 1 := by
    have r434 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
    have b435 := hb (x 11 3)
    have b436 := hb (x 11 11)
    clear * - r434 b435 b436 d426
    omega
  have d437 : (x 14 12).toNat = 0 := by
    have r438 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e439 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e440 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b441 := hb (x 11 3)
    have b442 := hb (x 12 2)
    have b443 := hb (x 13 13)
    have b444 := hb (x 14 12)
    clear * - r438 e439 e440 b441 b442 b443 b444 d433
    omega
  have d445 : (x 14 1 && x 14 12).toNat = 0 := by
    have r446 := hand2 (x 14 1) (x 14 12)
    have b447 := hb (x 14 12)
    have b448 := hb (x 14 1 && x 14 12)
    clear * - r446 b447 b448 d437
    omega
  have d449 : (x 13 13).toNat = 0 := by
    have r450 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e451 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e452 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b453 := hb (x 11 3)
    have b454 := hb (x 12 2)
    have b455 := hb (x 13 13)
    have b456 := hb (x 14 12)
    clear * - r450 e451 e452 b453 b454 b455 b456 d437 d433
    omega
  have d457 : (x 13 2 && x 13 13).toNat = 0 := by
    have r458 := hand2 (x 13 2) (x 13 13)
    have b459 := hb (x 13 13)
    have b460 := hb (x 13 2 && x 13 13)
    clear * - r458 b459 b460 d449
    omega
  have d461 : (x 12 2).toNat = 0 := by
    have r462 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e463 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e464 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b465 := hb (x 11 3)
    have b466 := hb (x 12 2)
    have b467 := hb (x 13 13)
    have b468 := hb (x 14 12)
    clear * - r462 e463 e464 b465 b466 b467 b468 d437 d449 d433
    omega
  have d469 : (x 9 1).toNat = 1 := by
    have r470 := hand1 (x 9 1) (x 9 14)
    have b471 := hb (x 9 1)
    have b472 := hb (x 9 1 && x 9 14)
    clear * - r470 b471 b472 d357
    omega
  have d473 : (x 10 14).toNat = 0 := by
    have r474 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b475 := hb (x 9 1)
    have b476 := hb (x 10 14)
    clear * - r474 b475 b476 d469
    omega
  have d477 : (x 10 1 && x 10 14).toNat = 0 := by
    have r478 := hand2 (x 10 1) (x 10 14)
    have b479 := hb (x 10 14)
    have b480 := hb (x 10 1 && x 10 14)
    clear * - r478 b479 b480 d473
    omega
  have d481 : (x 10 2).toNat = 0 := by
    have r482 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
    have b483 := hb (x 10 2)
    have b484 := hb (x 10 14)
    clear * - r482 b483 b484 d473
    omega
  have d485 : (x 9 2).toNat = 0 := by
    have r486 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e487 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e488 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b489 := hb (x 8 3)
    have b490 := hb (x 9 2)
    have b491 := hb (x 10 13)
    have b492 := hb (x 11 12)
    clear * - r486 e487 e488 b489 b490 b491 b492 d329 d345 d325
    omega
  have d493 : (x 11 13).toNat = 1 := by
    have r494 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b495 := hb (x 9 2)
    have b496 := hb (x 11 13)
    have b497 := hb (x 10 1 && x 10 14)
    clear * - r494 b495 b496 b497 d477 d485
    omega
  have d498 : (x 11 1).toNat = 1 := by
    have r499 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
    have b500 := hb (x 11 1)
    have b501 := hb (x 11 13)
    clear * - r499 b500 b501 d493
    omega
  have d502 : (x 12 14).toNat = 0 := by
    have r503 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b504 := hb (x 11 1)
    have b505 := hb (x 12 14)
    clear * - r503 b504 b505 d498
    omega
  have d506 : (x 12 1 && x 12 14).toNat = 0 := by
    have r507 := hand2 (x 12 1) (x 12 14)
    have b508 := hb (x 12 14)
    have b509 := hb (x 12 1 && x 12 14)
    clear * - r507 b508 b509 d502
    omega
  have d510 : (x 11 2).toNat = 1 := by
    have r511 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b512 := hb (x 11 2)
    have b513 := hb (x 13 13)
    have b514 := hb (x 12 1 && x 12 14)
    clear * - r511 b512 b513 b514 d449 d506
    omega
  have d515 : (x 13 12).toNat = 0 := by
    have r516 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e517 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e518 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b519 := hb (x 10 3)
    have b520 := hb (x 11 2)
    have b521 := hb (x 12 13)
    have b522 := hb (x 13 12)
    clear * - r516 e517 e518 b519 b520 b521 b522 d510
    omega
  have d523 : (x 13 4).toNat = 0 := by
    have r524 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
    have b525 := hb (x 13 4)
    have b526 := hb (x 13 12)
    clear * - r524 b525 b526 d515
    omega
  have d527 : (x 13 4 && x 13 14).toNat = 0 := by
    have r528 := hand1 (x 13 4) (x 13 14)
    have b529 := hb (x 13 4)
    have b530 := hb (x 13 4 && x 13 14)
    clear * - r528 b529 b530 d523
    omega
  have d531 : (x 12 13).toNat = 0 := by
    have r532 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e533 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e534 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b535 := hb (x 10 3)
    have b536 := hb (x 11 2)
    have b537 := hb (x 12 13)
    have b538 := hb (x 13 12)
    clear * - r532 e533 e534 b535 b536 b537 b538 d515 d510
    omega
  have d539 : (x 12 5).toNat = 0 := by
    have r540 : (x 12 5).toNat ≤ (x 12 13).toNat := himp _ _ (hp5 12)
    have b541 := hb (x 12 5)
    have b542 := hb (x 12 13)
    clear * - r540 b541 b542 d531
    omega
  have d543 : (x 12 3 && x 12 14).toNat = 0 := by
    have r544 := hand2 (x 12 3) (x 12 14)
    have b545 := hb (x 12 14)
    have b546 := hb (x 12 3 && x 12 14)
    clear * - r544 b545 b546 d502
    omega
  have d547 : (x 15 11).toNat = 1 := by
    have r548 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b549 := hb (x 11 4)
    have b550 := hb (x 15 11)
    have b551 := hb (x 14 1 && x 14 12)
    have b552 := hb (x 13 2 && x 13 13)
    have b553 := hb (x 12 3 && x 12 14)
    clear * - r548 b549 b550 b551 b552 b553 d445 d457 d543 d341
    omega
  have d554 : (x 15 3).toNat = 1 := by
    have r555 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
    have b556 := hb (x 15 3)
    have b557 := hb (x 15 11)
    clear * - r555 b556 b557 d547
    omega
  have d558 : (x 18 12).toNat = 0 := by
    have r559 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e560 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e561 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b562 := hb (x 15 3)
    have b563 := hb (x 16 2)
    have b564 := hb (x 17 13)
    have b565 := hb (x 18 12)
    clear * - r559 e560 e561 b562 b563 b564 b565 d554
    omega
  have d566 : (x 17 13).toNat = 0 := by
    have r567 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e568 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e569 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b570 := hb (x 15 3)
    have b571 := hb (x 16 2)
    have b572 := hb (x 17 13)
    have b573 := hb (x 18 12)
    clear * - r567 e568 e569 b570 b571 b572 b573 d558 d554
    omega
  have d574 : (x 16 2).toNat = 0 := by
    have r575 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e576 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e577 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b578 := hb (x 15 3)
    have b579 := hb (x 16 2)
    have b580 := hb (x 17 13)
    have b581 := hb (x 18 12)
    clear * - r575 e576 e577 b578 b579 b580 b581 d558 d566 d554
    omega
  have d582 : (x 12 12).toNat = 0 := by
    have r583 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e584 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e585 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b586 := hb (x 9 3)
    have b587 := hb (x 10 2)
    have b588 := hb (x 11 13)
    have b589 := hb (x 12 12)
    clear * - r583 e584 e585 b586 b587 b588 b589 d493 d481
    omega
  have d590 : (x 12 4).toNat = 0 := by
    have r591 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
    have b592 := hb (x 12 4)
    have b593 := hb (x 12 12)
    clear * - r591 b592 b593 d582
    omega
  have d594 : (x 9 3).toNat = 0 := by
    have r595 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e596 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e597 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b598 := hb (x 9 3)
    have b599 := hb (x 10 2)
    have b600 := hb (x 11 13)
    have b601 := hb (x 12 12)
    clear * - r595 e596 e597 b598 b599 b600 b601 d582 d493 d481
    omega
  have d602 : (x 9 3 && x 9 14).toNat = 0 := by
    have r603 := hand1 (x 9 3) (x 9 14)
    have b604 := hb (x 9 3)
    have b605 := hb (x 9 3 && x 9 14)
    clear * - r603 b604 b605 d594
    omega
  have d606 : (x 12 11).toNat = 1 := by
    have r607 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b608 := hb (x 8 4)
    have b609 := hb (x 12 11)
    have b610 := hb (x 11 1 && x 11 12)
    have b611 := hb (x 10 2 && x 10 13)
    have b612 := hb (x 9 3 && x 9 14)
    clear * - r607 b608 b609 b610 b611 b612 d337 d353 d602 d302
    omega
  have d613 : (x 12 3).toNat = 1 := by
    have r614 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
    have b615 := hb (x 12 3)
    have b616 := hb (x 12 11)
    clear * - r614 b615 b616 d606
    omega
  have d617 : (x 15 12).toNat = 0 := by
    have r618 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e619 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e620 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b621 := hb (x 12 3)
    have b622 := hb (x 13 2)
    have b623 := hb (x 14 13)
    have b624 := hb (x 15 12)
    clear * - r618 e619 e620 b621 b622 b623 b624 d613
    omega
  have d625 : (x 15 1 && x 15 12).toNat = 0 := by
    have r626 := hand2 (x 15 1) (x 15 12)
    have b627 := hb (x 15 12)
    have b628 := hb (x 15 1 && x 15 12)
    clear * - r626 b627 b628 d617
    omega
  have d629 : (x 15 2 && x 15 12).toNat = 0 := by
    have r630 := hand2 (x 15 2) (x 15 12)
    have b631 := hb (x 15 12)
    have b632 := hb (x 15 2 && x 15 12)
    clear * - r630 b631 b632 d617
    omega
  have d633 : (x 14 13).toNat = 0 := by
    have r634 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e635 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e636 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b637 := hb (x 12 3)
    have b638 := hb (x 13 2)
    have b639 := hb (x 14 13)
    have b640 := hb (x 15 12)
    clear * - r634 e635 e636 b637 b638 b639 b640 d617 d613
    omega
  have d641 : (x 14 2 && x 14 13).toNat = 0 := by
    have r642 := hand2 (x 14 2) (x 14 13)
    have b643 := hb (x 14 13)
    have b644 := hb (x 14 2 && x 14 13)
    clear * - r642 b643 b644 d633
    omega
  have d645 : (x 14 3 && x 14 13).toNat = 0 := by
    have r646 := hand2 (x 14 3) (x 14 13)
    have b647 := hb (x 14 13)
    have b648 := hb (x 14 3 && x 14 13)
    clear * - r646 b647 b648 d633
    omega
  have d649 : (x 13 1 && x 13 14).toNat = 1 := by
    have r650 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b651 := hb (x 12 2)
    have b652 := hb (x 14 13)
    have b653 := hb (x 13 1 && x 13 14)
    clear * - r650 b651 b652 b653 d633 d461
    omega
  have d654 : (x 13 1).toNat = 1 := by
    have r655 := hand1 (x 13 1) (x 13 14)
    have b656 := hb (x 13 1)
    have b657 := hb (x 13 1 && x 13 14)
    clear * - r655 b656 b657 d649
    omega
  have d658 : (x 14 14).toNat = 0 := by
    have r659 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b660 := hb (x 13 1)
    have b661 := hb (x 14 14)
    clear * - r659 b660 b661 d654
    omega
  have d662 : (x 14 1 && x 14 14).toNat = 0 := by
    have r663 := hand2 (x 14 1) (x 14 14)
    have b664 := hb (x 14 14)
    have b665 := hb (x 14 1 && x 14 14)
    clear * - r663 b664 b665 d658
    omega
  have d666 : (x 14 2).toNat = 0 := by
    have r667 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
    have b668 := hb (x 14 2)
    have b669 := hb (x 14 14)
    clear * - r667 b668 b669 d658
    omega
  have d670 : (x 13 2).toNat = 0 := by
    have r671 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e672 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e673 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b674 := hb (x 12 3)
    have b675 := hb (x 13 2)
    have b676 := hb (x 14 13)
    have b677 := hb (x 15 12)
    clear * - r671 e672 e673 b674 b675 b676 b677 d617 d633 d613
    omega
  have d678 : (x 15 13).toNat = 1 := by
    have r679 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b680 := hb (x 13 2)
    have b681 := hb (x 15 13)
    have b682 := hb (x 14 1 && x 14 14)
    clear * - r679 b680 b681 b682 d662 d670
    omega
  have d683 : (x 16 12).toNat = 0 := by
    have r684 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e685 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e686 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b687 := hb (x 13 3)
    have b688 := hb (x 14 2)
    have b689 := hb (x 15 13)
    have b690 := hb (x 16 12)
    clear * - r684 e685 e686 b687 b688 b689 b690 d678 d666
    omega
  have d691 : (x 13 3).toNat = 0 := by
    have r692 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e693 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e694 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b695 := hb (x 13 3)
    have b696 := hb (x 14 2)
    have b697 := hb (x 15 13)
    have b698 := hb (x 16 12)
    clear * - r692 e693 e694 b695 b696 b697 b698 d683 d678 d666
    omega
  have d699 : (x 13 3 && x 13 14).toNat = 0 := by
    have r700 := hand1 (x 13 3) (x 13 14)
    have b701 := hb (x 13 3)
    have b702 := hb (x 13 3 && x 13 14)
    clear * - r700 b701 b702 d691
    omega
  have d703 : (x 16 11).toNat = 1 := by
    have r704 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b705 := hb (x 12 4)
    have b706 := hb (x 16 11)
    have b707 := hb (x 15 1 && x 15 12)
    have b708 := hb (x 14 2 && x 14 13)
    have b709 := hb (x 13 3 && x 13 14)
    clear * - r704 b705 b706 b707 b708 b709 d625 d641 d699 d590
    omega
  have d710 : (x 16 3).toNat = 1 := by
    have r711 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
    have b712 := hb (x 16 3)
    have b713 := hb (x 16 11)
    clear * - r711 b712 b713 d703
    omega
  have d714 : (x 19 12).toNat = 0 := by
    have r715 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e716 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e717 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b718 := hb (x 16 3)
    have b719 := hb (x 17 2)
    have b720 := hb (x 18 13)
    have b721 := hb (x 19 12)
    clear * - r715 e716 e717 b718 b719 b720 b721 d710
    omega
  have d722 : (x 18 13).toNat = 0 := by
    have r723 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e724 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e725 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b726 := hb (x 16 3)
    have b727 := hb (x 17 2)
    have b728 := hb (x 18 13)
    have b729 := hb (x 19 12)
    clear * - r723 e724 e725 b726 b727 b728 b729 d714 d710
    omega
  have d730 : (x 17 1 && x 17 14).toNat = 1 := by
    have r731 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := by have q := hcov13 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b732 := hb (x 16 2)
    have b733 := hb (x 18 13)
    have b734 := hb (x 17 1 && x 17 14)
    clear * - r731 b732 b733 b734 d722 d574
    omega
  have d735 : (x 17 14).toNat = 1 := by
    have r736 := hand2 (x 17 1) (x 17 14)
    have b737 := hb (x 17 14)
    have b738 := hb (x 17 1 && x 17 14)
    clear * - r736 b737 b738 d730
    omega
  have d739 : (x 16 1).toNat = 0 := by
    have r740 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b741 := hb (x 16 1)
    have b742 := hb (x 17 14)
    clear * - r740 b741 b742 d735
    omega
  have d743 : (x 16 1 && x 16 11).toNat = 0 := by
    have r744 := hand1 (x 16 1) (x 16 11)
    have b745 := hb (x 16 1)
    have b746 := hb (x 16 1 && x 16 11)
    clear * - r744 b745 b746 d739
    omega
  have d747 : (x 17 2).toNat = 0 := by
    have r748 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e749 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e750 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b751 := hb (x 16 3)
    have b752 := hb (x 17 2)
    have b753 := hb (x 18 13)
    have b754 := hb (x 19 12)
    clear * - r748 e749 e750 b751 b752 b753 b754 d714 d722 d710
    omega
  have d755 : (x 17 10).toNat = 0 := by
    have r756 : (x 17 10).toNat ≤ (x 17 2).toNat := himp _ _ (hp10 17)
    have b757 := hb (x 17 2)
    have b758 := hb (x 17 10)
    clear * - r756 b757 b758 d747
    omega
  have r759 : 1 ≤ (x 17 10).toNat + (x 16 1 && x 16 11).toNat + (x 15 2 && x 15 12).toNat + (x 14 3 && x 14 13).toNat + (x 13 4 && x 13 14).toNat + (x 12 5).toNat := by have q := hcov10 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
  have b760 := hb (x 12 5)
  have b761 := hb (x 17 10)
  have b762 := hb (x 16 1 && x 16 11)
  have b763 := hb (x 15 2 && x 15 12)
  have b764 := hb (x 14 3 && x 14 13)
  have b765 := hb (x 13 4 && x 13 14)
  linarith only [r759, b760, b761, b762, b763, b764, b765, d755, d743, d629, d645, d527, d539]

theorem cycle_power_fifteen_tight_type_sequence_two_iff_three_core_b0 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 4).toNat = 0)
    (g1 : (x 3 4).toNat = 0)
    (g2 : (x 4 2).toNat = 0)
    (g3 : (x 4 4).toNat = 0)
    (g4 : (x 3 1 && x 3 12).toNat = 0)
    (g5 : (x 2 2 && x 2 13).toNat = 0)
    (g6 : (x 1 3 && x 1 14).toNat = 0)
    (g7 : (x 4 3 && x 4 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_two_iff_three_core_b0_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7
