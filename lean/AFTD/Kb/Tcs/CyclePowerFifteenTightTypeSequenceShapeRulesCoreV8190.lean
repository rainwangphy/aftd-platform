import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_shape_rules_core_v81_90

Topic: combinatorics   Node: 3e762fc12564

Provenance: helper lemma. Research thread RT-1, open case k = 15 (m = 4) of OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Experiment 9757: on the integer window [-24, 24] the layer-free tight-class model leaves 13 class types at the centre, none with an island; on [-32, 32] the six types {0,15}, {0,1,14,15}, {0..3,12..15}, {0..7,12..15}, {0..3,8..15}, {0..15}.

Window refutation for k = 15: in the layer-free tight-class model on the integer line (x p j: the class starting at p contains p + j; inner count 3 per vertex, distances 14, 12, 8 covered exactly once, the other distances covered, classes closed under the tight-class parent map), with x p 1 = x p 14 and x p 2 = x p 3 everywhere, the class at 0 cannot have bit 8 = 1 and bit 9 = 0.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v81_90_aux (x : ℤ → Fin 16 → Bool)
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
    (h114 : ∀ p, x p 1 = x p 14)
    (h23 : ∀ p, x p 2 = x p 3)
    (g0 : (x 0 8).toNat = 1) (g1 : (x 0 9).toNat = 0) : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d6237 : (x 0 3 && x 0 9).toNat = 0 := by
    have r6238 := hand2 (x 0 3) (x 0 9)
    have b6239 := hb (x 0 9)
    have b6240 := hb (x 0 3 && x 0 9)
    clear * - r6238 b6239 b6240 g1
    omega
  have d6241 : (x (-1) 9).toNat = 0 := by
    have r6242 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6243 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e6244 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e6245 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e6246 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e6247 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e6248 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b6249 := hb (x (-7) 7)
    have b6250 := hb (x (-6) 6)
    have b6251 := hb (x (-5) 5)
    have b6252 := hb (x (-4) 4)
    have b6253 := hb (x (-3) 11)
    have b6254 := hb (x (-2) 10)
    have b6255 := hb (x (-1) 9)
    have b6256 := hb (x 0 8)
    clear * - r6242 e6243 e6244 e6245 e6246 e6247 e6248 b6249 b6250 b6251 b6252 b6253 b6254 b6255 b6256 g0
    omega
  have d6257 : (x (-1) 3 && x (-1) 9).toNat = 0 := by
    have r6258 := hand2 (x (-1) 3) (x (-1) 9)
    have b6259 := hb (x (-1) 9)
    have b6260 := hb (x (-1) 3 && x (-1) 9)
    clear * - r6258 b6259 b6260 d6241
    omega
  have d6261 : (x (-1) 4 && x (-1) 9).toNat = 0 := by
    have r6262 := hand2 (x (-1) 4) (x (-1) 9)
    have b6263 := hb (x (-1) 9)
    have b6264 := hb (x (-1) 4 && x (-1) 9)
    clear * - r6262 b6263 b6264 d6241
    omega
  have d6265 : (x (-2) 10).toNat = 0 := by
    have r6266 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6267 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e6268 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e6269 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e6270 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e6271 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e6272 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b6273 := hb (x (-7) 7)
    have b6274 := hb (x (-6) 6)
    have b6275 := hb (x (-5) 5)
    have b6276 := hb (x (-4) 4)
    have b6277 := hb (x (-3) 11)
    have b6278 := hb (x (-2) 10)
    have b6279 := hb (x (-1) 9)
    have b6280 := hb (x 0 8)
    clear * - r6266 e6267 e6268 e6269 e6270 e6271 e6272 b6273 b6274 b6275 b6276 b6277 b6278 b6279 b6280 g0 d6241
    omega
  have d6281 : (x (-2) 1 && x (-2) 10).toNat = 0 := by
    have r6282 := hand2 (x (-2) 1) (x (-2) 10)
    have b6283 := hb (x (-2) 10)
    have b6284 := hb (x (-2) 1 && x (-2) 10)
    clear * - r6282 b6283 b6284 d6265
    omega
  have d6285 : (x (-2) 4 && x (-2) 10).toNat = 0 := by
    have r6286 := hand2 (x (-2) 4) (x (-2) 10)
    have b6287 := hb (x (-2) 10)
    have b6288 := hb (x (-2) 4 && x (-2) 10)
    clear * - r6286 b6287 b6288 d6265
    omega
  have d6289 : (x (-2) 5 && x (-2) 10).toNat = 0 := by
    have r6290 := hand2 (x (-2) 5) (x (-2) 10)
    have b6291 := hb (x (-2) 10)
    have b6292 := hb (x (-2) 5 && x (-2) 10)
    clear * - r6290 b6291 b6292 d6265
    omega
  have d6293 : (x (-3) 11).toNat = 0 := by
    have r6294 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6295 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e6296 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e6297 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e6298 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e6299 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e6300 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b6301 := hb (x (-7) 7)
    have b6302 := hb (x (-6) 6)
    have b6303 := hb (x (-5) 5)
    have b6304 := hb (x (-4) 4)
    have b6305 := hb (x (-3) 11)
    have b6306 := hb (x (-2) 10)
    have b6307 := hb (x (-1) 9)
    have b6308 := hb (x 0 8)
    clear * - r6294 e6295 e6296 e6297 e6298 e6299 e6300 b6301 b6302 b6303 b6304 b6305 b6306 b6307 b6308 g0 d6241 d6265
    omega
  have d6309 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
    have r6310 := hand2 (x (-3) 1) (x (-3) 11)
    have b6311 := hb (x (-3) 11)
    have b6312 := hb (x (-3) 1 && x (-3) 11)
    clear * - r6310 b6311 b6312 d6293
    omega
  have d6313 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
    have r6314 := hand2 (x (-3) 2) (x (-3) 11)
    have b6315 := hb (x (-3) 11)
    have b6316 := hb (x (-3) 2 && x (-3) 11)
    clear * - r6314 b6315 b6316 d6293
    omega
  have d6317 : (x (-3) 5 && x (-3) 11).toNat = 0 := by
    have r6318 := hand2 (x (-3) 5) (x (-3) 11)
    have b6319 := hb (x (-3) 11)
    have b6320 := hb (x (-3) 5 && x (-3) 11)
    clear * - r6318 b6319 b6320 d6293
    omega
  have d6321 : (x (-3) 6 && x (-3) 11).toNat = 0 := by
    have r6322 := hand2 (x (-3) 6) (x (-3) 11)
    have b6323 := hb (x (-3) 11)
    have b6324 := hb (x (-3) 6 && x (-3) 11)
    clear * - r6322 b6323 b6324 d6293
    omega
  have d6325 : (x (-4) 4).toNat = 0 := by
    have r6326 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6327 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e6328 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e6329 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e6330 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e6331 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e6332 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b6333 := hb (x (-7) 7)
    have b6334 := hb (x (-6) 6)
    have b6335 := hb (x (-5) 5)
    have b6336 := hb (x (-4) 4)
    have b6337 := hb (x (-3) 11)
    have b6338 := hb (x (-2) 10)
    have b6339 := hb (x (-1) 9)
    have b6340 := hb (x 0 8)
    clear * - r6326 e6327 e6328 e6329 e6330 e6331 e6332 b6333 b6334 b6335 b6336 b6337 b6338 b6339 b6340 g0 d6241 d6265 d6293
    omega
  have d6341 : (x (-4) 4 && x (-4) 13).toNat = 0 := by
    have r6342 := hand1 (x (-4) 4) (x (-4) 13)
    have b6343 := hb (x (-4) 4)
    have b6344 := hb (x (-4) 4 && x (-4) 13)
    clear * - r6342 b6343 b6344 d6325
    omega
  have d6345 : (x (-4) 4 && x (-4) 11).toNat = 0 := by
    have r6346 := hand1 (x (-4) 4) (x (-4) 11)
    have b6347 := hb (x (-4) 4)
    have b6348 := hb (x (-4) 4 && x (-4) 11)
    clear * - r6346 b6347 b6348 d6325
    omega
  have d6349 : (x (-4) 4 && x (-4) 10).toNat = 0 := by
    have r6350 := hand1 (x (-4) 4) (x (-4) 10)
    have b6351 := hb (x (-4) 4)
    have b6352 := hb (x (-4) 4 && x (-4) 10)
    clear * - r6350 b6351 b6352 d6325
    omega
  have d6353 : (x (-4) 4 && x (-4) 8).toNat = 0 := by
    have r6354 := hand1 (x (-4) 4) (x (-4) 8)
    have b6355 := hb (x (-4) 4)
    have b6356 := hb (x (-4) 4 && x (-4) 8)
    clear * - r6354 b6355 b6356 d6325
    omega
  have d6357 : (x (-5) 5).toNat = 0 := by
    have r6358 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6359 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e6360 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e6361 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e6362 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e6363 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e6364 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b6365 := hb (x (-7) 7)
    have b6366 := hb (x (-6) 6)
    have b6367 := hb (x (-5) 5)
    have b6368 := hb (x (-4) 4)
    have b6369 := hb (x (-3) 11)
    have b6370 := hb (x (-2) 10)
    have b6371 := hb (x (-1) 9)
    have b6372 := hb (x 0 8)
    clear * - r6358 e6359 e6360 e6361 e6362 e6363 e6364 b6365 b6366 b6367 b6368 b6369 b6370 b6371 b6372 g0 d6241 d6265 d6293 d6325
    omega
  have d6373 : (x (-5) 5 && x (-5) 14).toNat = 0 := by
    have r6374 := hand1 (x (-5) 5) (x (-5) 14)
    have b6375 := hb (x (-5) 5)
    have b6376 := hb (x (-5) 5 && x (-5) 14)
    clear * - r6374 b6375 b6376 d6357
    omega
  have d6377 : (x (-5) 5 && x (-5) 12).toNat = 0 := by
    have r6378 := hand1 (x (-5) 5) (x (-5) 12)
    have b6379 := hb (x (-5) 5)
    have b6380 := hb (x (-5) 5 && x (-5) 12)
    clear * - r6378 b6379 b6380 d6357
    omega
  have d6381 : (x (-5) 5 && x (-5) 11).toNat = 0 := by
    have r6382 := hand1 (x (-5) 5) (x (-5) 11)
    have b6383 := hb (x (-5) 5)
    have b6384 := hb (x (-5) 5 && x (-5) 11)
    clear * - r6382 b6383 b6384 d6357
    omega
  have d6385 : (x (-5) 5 && x (-5) 9).toNat = 0 := by
    have r6386 := hand1 (x (-5) 5) (x (-5) 9)
    have b6387 := hb (x (-5) 5)
    have b6388 := hb (x (-5) 5 && x (-5) 9)
    clear * - r6386 b6387 b6388 d6357
    omega
  have d6389 : (x (-6) 6).toNat = 0 := by
    have r6390 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6391 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e6392 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e6393 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e6394 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e6395 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e6396 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b6397 := hb (x (-7) 7)
    have b6398 := hb (x (-6) 6)
    have b6399 := hb (x (-5) 5)
    have b6400 := hb (x (-4) 4)
    have b6401 := hb (x (-3) 11)
    have b6402 := hb (x (-2) 10)
    have b6403 := hb (x (-1) 9)
    have b6404 := hb (x 0 8)
    clear * - r6390 e6391 e6392 e6393 e6394 e6395 e6396 b6397 b6398 b6399 b6400 b6401 b6402 b6403 b6404 g0 d6241 d6265 d6293 d6325 d6357
    omega
  have d6405 : (x (-6) 6 && x (-6) 13).toNat = 0 := by
    have r6406 := hand1 (x (-6) 6) (x (-6) 13)
    have b6407 := hb (x (-6) 6)
    have b6408 := hb (x (-6) 6 && x (-6) 13)
    clear * - r6406 b6407 b6408 d6389
    omega
  have d6409 : (x (-6) 6 && x (-6) 12).toNat = 0 := by
    have r6410 := hand1 (x (-6) 6) (x (-6) 12)
    have b6411 := hb (x (-6) 6)
    have b6412 := hb (x (-6) 6 && x (-6) 12)
    clear * - r6410 b6411 b6412 d6389
    omega
  have d6413 : (x (-6) 6 && x (-6) 10).toNat = 0 := by
    have r6414 := hand1 (x (-6) 6) (x (-6) 10)
    have b6415 := hb (x (-6) 6)
    have b6416 := hb (x (-6) 6 && x (-6) 10)
    clear * - r6414 b6415 b6416 d6389
    omega
  have d6417 : (x (-7) 7).toNat = 0 := by
    have r6418 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6419 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e6420 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e6421 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e6422 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e6423 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e6424 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b6425 := hb (x (-7) 7)
    have b6426 := hb (x (-6) 6)
    have b6427 := hb (x (-5) 5)
    have b6428 := hb (x (-4) 4)
    have b6429 := hb (x (-3) 11)
    have b6430 := hb (x (-2) 10)
    have b6431 := hb (x (-1) 9)
    have b6432 := hb (x 0 8)
    clear * - r6418 e6419 e6420 e6421 e6422 e6423 e6424 b6425 b6426 b6427 b6428 b6429 b6430 b6431 b6432 g0 d6241 d6265 d6293 d6325 d6357 d6389
    omega
  have d6433 : (x (-7) 7 && x (-7) 14).toNat = 0 := by
    have r6434 := hand1 (x (-7) 7) (x (-7) 14)
    have b6435 := hb (x (-7) 7)
    have b6436 := hb (x (-7) 7 && x (-7) 14)
    clear * - r6434 b6435 b6436 d6417
    omega
  have d6437 : (x (-7) 7 && x (-7) 13).toNat = 0 := by
    have r6438 := hand1 (x (-7) 7) (x (-7) 13)
    have b6439 := hb (x (-7) 7)
    have b6440 := hb (x (-7) 7 && x (-7) 13)
    clear * - r6438 b6439 b6440 d6417
    omega
  have d6441 : (x (-7) 7 && x (-7) 11).toNat = 0 := by
    have r6442 := hand1 (x (-7) 7) (x (-7) 11)
    have b6443 := hb (x (-7) 7)
    have b6444 := hb (x (-7) 7 && x (-7) 11)
    clear * - r6442 b6443 b6444 d6417
    omega
  cases h6445 : x 0 1
  · have f6446 : (x 0 1).toNat = 0 := by rw [h6445]; rfl
    have d6447 : (x 0 14).toNat = 0 := by
      have r6448 : (x 0 1).toNat = (x 0 14).toNat := congrArg Bool.toNat (h114 0)
      have b6449 := hb (x 0 1)
      have b6450 := hb (x 0 14)
      clear * - r6448 b6449 b6450 f6446
      omega
    have d6451 : (x 0 6).toNat = 0 := by
      have r6452 : (x 0 6).toNat ≤ (x 0 14).toNat := himp _ _ (hp6 0)
      have b6453 := hb (x 0 6)
      have b6454 := hb (x 0 14)
      clear * - r6452 b6453 b6454 d6447
      omega
    have d6455 : (x 0 2).toNat = 0 := by
      have r6456 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
      have b6457 := hb (x 0 2)
      have b6458 := hb (x 0 14)
      clear * - r6456 b6457 b6458 d6447
      omega
    have d6459 : (x 0 2 && x 0 12).toNat = 0 := by
      have r6460 := hand1 (x 0 2) (x 0 12)
      have b6461 := hb (x 0 2)
      have b6462 := hb (x 0 2 && x 0 12)
      clear * - r6460 b6461 b6462 d6455
      omega
    have d6463 : (x 0 2 && x 0 8).toNat = 0 := by
      have r6464 := hand1 (x 0 2) (x 0 8)
      have b6465 := hb (x 0 2)
      have b6466 := hb (x 0 2 && x 0 8)
      clear * - r6464 b6465 b6466 d6455
      omega
    have d6467 : (x 0 3).toNat = 0 := by
      have r6468 : (x 0 2).toNat = (x 0 3).toNat := congrArg Bool.toNat (h23 0)
      have b6469 := hb (x 0 2)
      have b6470 := hb (x 0 3)
      clear * - r6468 b6469 b6470 d6455
      omega
    have d6471 : (x 0 3 && x 0 8).toNat = 0 := by
      have r6472 := hand1 (x 0 3) (x 0 8)
      have b6473 := hb (x 0 3)
      have b6474 := hb (x 0 3 && x 0 8)
      clear * - r6472 b6473 b6474 d6467
      omega
    have d6475 : (x 1 14).toNat = 1 := by
      have r6476 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6477 := hb (x 0 1)
      have b6478 := hb (x 1 14)
      clear * - r6476 b6477 b6478 f6446
      omega
    have d6479 : (x 1 1).toNat = 1 := by
      have r6480 : (x 1 1).toNat = (x 1 14).toNat := congrArg Bool.toNat (h114 1)
      have b6481 := hb (x 1 1)
      have b6482 := hb (x 1 14)
      clear * - r6480 b6481 b6482 d6475
      omega
    have d6483 : (x 2 14).toNat = 0 := by
      have r6484 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6485 := hb (x 1 1)
      have b6486 := hb (x 2 14)
      clear * - r6484 b6485 b6486 d6479
      omega
    have d6487 : (x 2 1).toNat = 0 := by
      have r6488 : (x 2 1).toNat = (x 2 14).toNat := congrArg Bool.toNat (h114 2)
      have b6489 := hb (x 2 1)
      have b6490 := hb (x 2 14)
      clear * - r6488 b6489 b6490 d6483
      omega
    have d6491 : (x 2 1 && x 2 6).toNat = 0 := by
      have r6492 := hand1 (x 2 1) (x 2 6)
      have b6493 := hb (x 2 1)
      have b6494 := hb (x 2 1 && x 2 6)
      clear * - r6492 b6493 b6494 d6487
      omega
    have d6495 : (x 2 13).toNat = 0 := by
      have r6496 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
      have b6497 := hb (x 2 1)
      have b6498 := hb (x 2 13)
      clear * - r6496 b6497 b6498 d6487
      omega
    have d6499 : (x 2 4 && x 2 13).toNat = 0 := by
      have r6500 := hand2 (x 2 4) (x 2 13)
      have b6501 := hb (x 2 13)
      have b6502 := hb (x 2 4 && x 2 13)
      clear * - r6500 b6501 b6502 d6495
      omega
    have d6503 : (x 2 5).toNat = 0 := by
      have r6504 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
      have b6505 := hb (x 2 5)
      have b6506 := hb (x 2 13)
      clear * - r6504 b6505 b6506 d6495
      omega
    have d6507 : (x 3 14).toNat = 1 := by
      have r6508 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6509 := hb (x 2 1)
      have b6510 := hb (x 3 14)
      clear * - r6508 b6509 b6510 d6487
      omega
    have d6511 : (x 3 1).toNat = 1 := by
      have r6512 : (x 3 1).toNat = (x 3 14).toNat := congrArg Bool.toNat (h114 3)
      have b6513 := hb (x 3 1)
      have b6514 := hb (x 3 14)
      clear * - r6512 b6513 b6514 d6507
      omega
    have d6515 : (x 4 14).toNat = 0 := by
      have r6516 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6517 := hb (x 3 1)
      have b6518 := hb (x 4 14)
      clear * - r6516 b6517 b6518 d6511
      omega
    have d6519 : (x 4 1).toNat = 0 := by
      have r6520 : (x 4 1).toNat = (x 4 14).toNat := congrArg Bool.toNat (h114 4)
      have b6521 := hb (x 4 1)
      have b6522 := hb (x 4 14)
      clear * - r6520 b6521 b6522 d6515
      omega
    have d6523 : (x 5 14).toNat = 1 := by
      have r6524 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6525 := hb (x 4 1)
      have b6526 := hb (x 5 14)
      clear * - r6524 b6525 b6526 d6519
      omega
    have d6527 : (x 5 1).toNat = 1 := by
      have r6528 : (x 5 1).toNat = (x 5 14).toNat := congrArg Bool.toNat (h114 5)
      have b6529 := hb (x 5 1)
      have b6530 := hb (x 5 14)
      clear * - r6528 b6529 b6530 d6523
      omega
    have d6531 : (x 6 14).toNat = 0 := by
      have r6532 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6533 := hb (x 5 1)
      have b6534 := hb (x 6 14)
      clear * - r6532 b6533 b6534 d6527
      omega
    have d6535 : (x 6 1).toNat = 0 := by
      have r6536 : (x 6 1).toNat = (x 6 14).toNat := congrArg Bool.toNat (h114 6)
      have b6537 := hb (x 6 1)
      have b6538 := hb (x 6 14)
      clear * - r6536 b6537 b6538 d6531
      omega
    have d6539 : (x 6 9).toNat = 0 := by
      have r6540 : (x 6 9).toNat ≤ (x 6 1).toNat := himp _ _ (hp9 6)
      have b6541 := hb (x 6 1)
      have b6542 := hb (x 6 9)
      clear * - r6540 b6541 b6542 d6535
      omega
    have d6543 : (x 7 14).toNat = 1 := by
      have r6544 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6545 := hb (x 6 1)
      have b6546 := hb (x 7 14)
      clear * - r6544 b6545 b6546 d6535
      omega
    have d6547 : (x 7 1).toNat = 1 := by
      have r6548 : (x 7 1).toNat = (x 7 14).toNat := congrArg Bool.toNat (h114 7)
      have b6549 := hb (x 7 1)
      have b6550 := hb (x 7 14)
      clear * - r6548 b6549 b6550 d6543
      omega
    have d6551 : (x 6 2).toNat = 0 := by
      have r6552 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
      have b6553 := hb (x 6 2)
      have b6554 := hb (x 6 14)
      clear * - r6552 b6553 b6554 d6531
      omega
    have d6555 : (x 4 2).toNat = 0 := by
      have r6556 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
      have b6557 := hb (x 4 2)
      have b6558 := hb (x 4 14)
      clear * - r6556 b6557 b6558 d6515
      omega
    have d6559 : (x 4 2 && x 4 11).toNat = 0 := by
      have r6560 := hand1 (x 4 2) (x 4 11)
      have b6561 := hb (x 4 2)
      have b6562 := hb (x 4 2 && x 4 11)
      clear * - r6560 b6561 b6562 d6555
      omega
    have d6563 : (x 4 3).toNat = 0 := by
      have r6564 : (x 4 2).toNat = (x 4 3).toNat := congrArg Bool.toNat (h23 4)
      have b6565 := hb (x 4 2)
      have b6566 := hb (x 4 3)
      clear * - r6564 b6565 b6566 d6555
      omega
    have d6567 : (x 4 11).toNat = 0 := by
      have r6568 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
      have b6569 := hb (x 4 3)
      have b6570 := hb (x 4 11)
      clear * - r6568 b6569 b6570 d6563
      omega
    have d6571 : (x 2 6).toNat = 0 := by
      have r6572 : (x 2 6).toNat ≤ (x 2 14).toNat := himp _ _ (hp6 2)
      have b6573 := hb (x 2 6)
      have b6574 := hb (x 2 14)
      clear * - r6572 b6573 b6574 d6483
      omega
    have d6575 : (x 2 2).toNat = 0 := by
      have r6576 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b6577 := hb (x 2 2)
      have b6578 := hb (x 2 14)
      clear * - r6576 b6577 b6578 d6483
      omega
    have d6579 : (x 2 10).toNat = 0 := by
      have r6580 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
      have b6581 := hb (x 2 2)
      have b6582 := hb (x 2 10)
      clear * - r6580 b6581 b6582 d6575
      omega
    have d6583 : (x (-1) 1).toNat = 1 := by
      have r6584 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6585 := hb (x (-1) 1)
      have b6586 := hb (x 0 14)
      clear * - r6584 b6585 b6586 d6447
      omega
    have d6587 : (x (-1) 14).toNat = 1 := by
      have r6588 : (x (-1) 1).toNat = (x (-1) 14).toNat := congrArg Bool.toNat (h114 (-1))
      have b6589 := hb (x (-1) 1)
      have b6590 := hb (x (-1) 14)
      clear * - r6588 b6589 b6590 d6583
      omega
    have d6591 : (x (-2) 1).toNat = 0 := by
      have r6592 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6593 := hb (x (-2) 1)
      have b6594 := hb (x (-1) 14)
      clear * - r6592 b6593 b6594 d6587
      omega
    have d6595 : (x (-2) 14).toNat = 0 := by
      have r6596 : (x (-2) 1).toNat = (x (-2) 14).toNat := congrArg Bool.toNat (h114 (-2))
      have b6597 := hb (x (-2) 1)
      have b6598 := hb (x (-2) 14)
      clear * - r6596 b6597 b6598 d6591
      omega
    have d6599 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
      have r6600 := hand2 (x (-2) 4) (x (-2) 14)
      have b6601 := hb (x (-2) 14)
      have b6602 := hb (x (-2) 4 && x (-2) 14)
      clear * - r6600 b6601 b6602 d6595
      omega
    have d6603 : (x (-2) 6).toNat = 0 := by
      have r6604 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
      have b6605 := hb (x (-2) 6)
      have b6606 := hb (x (-2) 14)
      clear * - r6604 b6605 b6606 d6595
      omega
    have d6607 : (x (-2) 2 && x (-2) 6).toNat = 0 := by
      have r6608 := hand2 (x (-2) 2) (x (-2) 6)
      have b6609 := hb (x (-2) 6)
      have b6610 := hb (x (-2) 2 && x (-2) 6)
      clear * - r6608 b6609 b6610 d6603
      omega
    have d6611 : (x (-2) 2).toNat = 0 := by
      have r6612 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
      have b6613 := hb (x (-2) 2)
      have b6614 := hb (x (-2) 14)
      clear * - r6612 b6613 b6614 d6595
      omega
    have d6615 : (x (-2) 2 && x (-2) 8).toNat = 0 := by
      have r6616 := hand1 (x (-2) 2) (x (-2) 8)
      have b6617 := hb (x (-2) 2)
      have b6618 := hb (x (-2) 2 && x (-2) 8)
      clear * - r6616 b6617 b6618 d6611
      omega
    have d6619 : (x (-2) 9).toNat = 0 := by
      have r6620 : (x (-2) 9).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp9 (-2))
      have b6621 := hb (x (-2) 1)
      have b6622 := hb (x (-2) 9)
      clear * - r6620 b6621 b6622 d6591
      omega
    have d6623 : (x (-3) 1).toNat = 1 := by
      have r6624 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6625 := hb (x (-3) 1)
      have b6626 := hb (x (-2) 14)
      clear * - r6624 b6625 b6626 d6595
      omega
    have d6627 : (x (-3) 14).toNat = 1 := by
      have r6628 : (x (-3) 1).toNat = (x (-3) 14).toNat := congrArg Bool.toNat (h114 (-3))
      have b6629 := hb (x (-3) 1)
      have b6630 := hb (x (-3) 14)
      clear * - r6628 b6629 b6630 d6623
      omega
    have d6631 : (x (-4) 1).toNat = 0 := by
      have r6632 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6633 := hb (x (-4) 1)
      have b6634 := hb (x (-3) 14)
      clear * - r6632 b6633 b6634 d6627
      omega
    have d6635 : (x (-4) 14).toNat = 0 := by
      have r6636 : (x (-4) 1).toNat = (x (-4) 14).toNat := congrArg Bool.toNat (h114 (-4))
      have b6637 := hb (x (-4) 1)
      have b6638 := hb (x (-4) 14)
      clear * - r6636 b6637 b6638 d6631
      omega
    have d6639 : (x (-4) 6).toNat = 0 := by
      have r6640 : (x (-4) 6).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp6 (-4))
      have b6641 := hb (x (-4) 6)
      have b6642 := hb (x (-4) 14)
      clear * - r6640 b6641 b6642 d6635
      omega
    have d6643 : (x (-4) 6 && x (-4) 12).toNat = 0 := by
      have r6644 := hand1 (x (-4) 6) (x (-4) 12)
      have b6645 := hb (x (-4) 6)
      have b6646 := hb (x (-4) 6 && x (-4) 12)
      clear * - r6644 b6645 b6646 d6639
      omega
    have d6647 : (x (-4) 2).toNat = 0 := by
      have r6648 : (x (-4) 2).toNat ≤ (x (-4) 14).toNat := himp _ _ (hp2 (-4))
      have b6649 := hb (x (-4) 2)
      have b6650 := hb (x (-4) 14)
      clear * - r6648 b6649 b6650 d6635
      omega
    have d6651 : (x (-4) 3).toNat = 0 := by
      have r6652 : (x (-4) 2).toNat = (x (-4) 3).toNat := congrArg Bool.toNat (h23 (-4))
      have b6653 := hb (x (-4) 2)
      have b6654 := hb (x (-4) 3)
      clear * - r6652 b6653 b6654 d6647
      omega
    have d6655 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
      have r6656 := hand1 (x (-4) 3) (x (-4) 12)
      have b6657 := hb (x (-4) 3)
      have b6658 := hb (x (-4) 3 && x (-4) 12)
      clear * - r6656 b6657 b6658 d6651
      omega
    have d6659 : (x (-4) 11).toNat = 0 := by
      have r6660 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
      have b6661 := hb (x (-4) 3)
      have b6662 := hb (x (-4) 11)
      clear * - r6660 b6661 b6662 d6651
      omega
    have d6663 : (x (-4) 10).toNat = 0 := by
      have r6664 : (x (-4) 10).toNat ≤ (x (-4) 2).toNat := himp _ _ (hp10 (-4))
      have b6665 := hb (x (-4) 2)
      have b6666 := hb (x (-4) 10)
      clear * - r6664 b6665 b6666 d6647
      omega
    have d6667 : (x (-5) 1).toNat = 1 := by
      have r6668 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6669 := hb (x (-5) 1)
      have b6670 := hb (x (-4) 14)
      clear * - r6668 b6669 b6670 d6635
      omega
    have d6671 : (x (-5) 14).toNat = 1 := by
      have r6672 : (x (-5) 1).toNat = (x (-5) 14).toNat := congrArg Bool.toNat (h114 (-5))
      have b6673 := hb (x (-5) 1)
      have b6674 := hb (x (-5) 14)
      clear * - r6672 b6673 b6674 d6667
      omega
    have d6675 : (x (-6) 1).toNat = 0 := by
      have r6676 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6677 := hb (x (-6) 1)
      have b6678 := hb (x (-5) 14)
      clear * - r6676 b6677 b6678 d6671
      omega
    have d6679 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
      have r6680 := hand1 (x (-6) 1) (x (-6) 14)
      have b6681 := hb (x (-6) 1)
      have b6682 := hb (x (-6) 1 && x (-6) 14)
      clear * - r6680 b6681 b6682 d6675
      omega
    have d6683 : (x (-6) 1 && x (-6) 12).toNat = 0 := by
      have r6684 := hand1 (x (-6) 1) (x (-6) 12)
      have b6685 := hb (x (-6) 1)
      have b6686 := hb (x (-6) 1 && x (-6) 12)
      clear * - r6684 b6685 b6686 d6675
      omega
    have d6687 : (x (-6) 1 && x (-6) 10).toNat = 0 := by
      have r6688 := hand1 (x (-6) 1) (x (-6) 10)
      have b6689 := hb (x (-6) 1)
      have b6690 := hb (x (-6) 1 && x (-6) 10)
      clear * - r6688 b6689 b6690 d6675
      omega
    have d6691 : (x (-6) 14).toNat = 0 := by
      have r6692 : (x (-6) 1).toNat = (x (-6) 14).toNat := congrArg Bool.toNat (h114 (-6))
      have b6693 := hb (x (-6) 1)
      have b6694 := hb (x (-6) 14)
      clear * - r6692 b6693 b6694 d6675
      omega
    have d6695 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
      have r6696 := hand2 (x (-6) 5) (x (-6) 14)
      have b6697 := hb (x (-6) 14)
      have b6698 := hb (x (-6) 5 && x (-6) 14)
      clear * - r6696 b6697 b6698 d6691
      omega
    have d6699 : (x (-6) 8 && x (-6) 14).toNat = 0 := by
      have r6700 := hand2 (x (-6) 8) (x (-6) 14)
      have b6701 := hb (x (-6) 14)
      have b6702 := hb (x (-6) 8 && x (-6) 14)
      clear * - r6700 b6701 b6702 d6691
      omega
    have d6703 : (x (-6) 9 && x (-6) 14).toNat = 0 := by
      have r6704 := hand2 (x (-6) 9) (x (-6) 14)
      have b6705 := hb (x (-6) 14)
      have b6706 := hb (x (-6) 9 && x (-6) 14)
      clear * - r6704 b6705 b6706 d6691
      omega
    have d6707 : (x (-6) 2).toNat = 0 := by
      have r6708 : (x (-6) 2).toNat ≤ (x (-6) 14).toNat := himp _ _ (hp2 (-6))
      have b6709 := hb (x (-6) 2)
      have b6710 := hb (x (-6) 14)
      clear * - r6708 b6709 b6710 d6691
      omega
    have d6711 : (x (-6) 10).toNat = 0 := by
      have r6712 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
      have b6713 := hb (x (-6) 2)
      have b6714 := hb (x (-6) 10)
      clear * - r6712 b6713 b6714 d6707
      omega
    have d6715 : (x (-6) 13).toNat = 0 := by
      have r6716 : (x (-6) 13).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp13 (-6))
      have b6717 := hb (x (-6) 1)
      have b6718 := hb (x (-6) 13)
      clear * - r6716 b6717 b6718 d6675
      omega
    have d6719 : (x (-6) 5).toNat = 0 := by
      have r6720 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
      have b6721 := hb (x (-6) 5)
      have b6722 := hb (x (-6) 13)
      clear * - r6720 b6721 b6722 d6715
      omega
    have d6723 : (x (-6) 9).toNat = 0 := by
      have r6724 : (x (-6) 9).toNat ≤ (x (-6) 1).toNat := himp _ _ (hp9 (-6))
      have b6725 := hb (x (-6) 1)
      have b6726 := hb (x (-6) 9)
      clear * - r6724 b6725 b6726 d6675
      omega
    have d6727 : (x (-7) 1).toNat = 1 := by
      have r6728 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6729 := hb (x (-7) 1)
      have b6730 := hb (x (-6) 14)
      clear * - r6728 b6729 b6730 d6691
      omega
    have d6731 : (x (-7) 14).toNat = 1 := by
      have r6732 : (x (-7) 1).toNat = (x (-7) 14).toNat := congrArg Bool.toNat (h114 (-7))
      have b6733 := hb (x (-7) 1)
      have b6734 := hb (x (-7) 14)
      clear * - r6732 b6733 b6734 d6727
      omega
    have d6735 : (x (-8) 1).toNat = 0 := by
      have r6736 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6737 := hb (x (-8) 1)
      have b6738 := hb (x (-7) 14)
      clear * - r6736 b6737 b6738 d6731
      omega
    have d6739 : (x (-8) 14).toNat = 0 := by
      have r6740 : (x (-8) 1).toNat = (x (-8) 14).toNat := congrArg Bool.toNat (h114 (-8))
      have b6741 := hb (x (-8) 1)
      have b6742 := hb (x (-8) 14)
      clear * - r6740 b6741 b6742 d6735
      omega
    have d6743 : (x (-8) 3 && x (-8) 14).toNat = 0 := by
      have r6744 := hand2 (x (-8) 3) (x (-8) 14)
      have b6745 := hb (x (-8) 14)
      have b6746 := hb (x (-8) 3 && x (-8) 14)
      clear * - r6744 b6745 b6746 d6739
      omega
    have d6747 : (x (-8) 8 && x (-8) 14).toNat = 0 := by
      have r6748 := hand2 (x (-8) 8) (x (-8) 14)
      have b6749 := hb (x (-8) 14)
      have b6750 := hb (x (-8) 8 && x (-8) 14)
      clear * - r6748 b6749 b6750 d6739
      omega
    have d6751 : (x (-8) 2).toNat = 0 := by
      have r6752 : (x (-8) 2).toNat ≤ (x (-8) 14).toNat := himp _ _ (hp2 (-8))
      have b6753 := hb (x (-8) 2)
      have b6754 := hb (x (-8) 14)
      clear * - r6752 b6753 b6754 d6739
      omega
    have d6755 : (x (-8) 3).toNat = 0 := by
      have r6756 : (x (-8) 2).toNat = (x (-8) 3).toNat := congrArg Bool.toNat (h23 (-8))
      have b6757 := hb (x (-8) 2)
      have b6758 := hb (x (-8) 3)
      clear * - r6756 b6757 b6758 d6751
      omega
    have d6759 : (x (-8) 3 && x (-8) 12).toNat = 0 := by
      have r6760 := hand1 (x (-8) 3) (x (-8) 12)
      have b6761 := hb (x (-8) 3)
      have b6762 := hb (x (-8) 3 && x (-8) 12)
      clear * - r6760 b6761 b6762 d6755
      omega
    have d6763 : (x (-8) 11).toNat = 0 := by
      have r6764 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
      have b6765 := hb (x (-8) 3)
      have b6766 := hb (x (-8) 11)
      clear * - r6764 b6765 b6766 d6755
      omega
    have d6767 : (x (-8) 10).toNat = 0 := by
      have r6768 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
      have b6769 := hb (x (-8) 2)
      have b6770 := hb (x (-8) 10)
      clear * - r6768 b6769 b6770 d6751
      omega
    have d6771 : (x (-9) 1).toNat = 1 := by
      have r6772 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6773 := hb (x (-9) 1)
      have b6774 := hb (x (-8) 14)
      clear * - r6772 b6773 b6774 d6739
      omega
    have d6775 : (x (-9) 14).toNat = 1 := by
      have r6776 : (x (-9) 1).toNat = (x (-9) 14).toNat := congrArg Bool.toNat (h114 (-9))
      have b6777 := hb (x (-9) 1)
      have b6778 := hb (x (-9) 14)
      clear * - r6776 b6777 b6778 d6771
      omega
    have d6779 : (x (-10) 1).toNat = 0 := by
      have r6780 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b6781 := hb (x (-10) 1)
      have b6782 := hb (x (-9) 14)
      clear * - r6780 b6781 b6782 d6775
      omega
    have d6783 : (x (-10) 14).toNat = 0 := by
      have r6784 : (x (-10) 1).toNat = (x (-10) 14).toNat := congrArg Bool.toNat (h114 (-10))
      have b6785 := hb (x (-10) 1)
      have b6786 := hb (x (-10) 14)
      clear * - r6784 b6785 b6786 d6779
      omega
    have d6787 : (x (-10) 5 && x (-10) 14).toNat = 0 := by
      have r6788 := hand2 (x (-10) 5) (x (-10) 14)
      have b6789 := hb (x (-10) 14)
      have b6790 := hb (x (-10) 5 && x (-10) 14)
      clear * - r6788 b6789 b6790 d6783
      omega
    have d6791 : (x (-10) 2).toNat = 0 := by
      have r6792 : (x (-10) 2).toNat ≤ (x (-10) 14).toNat := himp _ _ (hp2 (-10))
      have b6793 := hb (x (-10) 2)
      have b6794 := hb (x (-10) 14)
      clear * - r6792 b6793 b6794 d6783
      omega
    have d6795 : (x (-10) 2 && x (-10) 12).toNat = 0 := by
      have r6796 := hand1 (x (-10) 2) (x (-10) 12)
      have b6797 := hb (x (-10) 2)
      have b6798 := hb (x (-10) 2 && x (-10) 12)
      clear * - r6796 b6797 b6798 d6791
      omega
    have d6799 : (x (-10) 10).toNat = 0 := by
      have r6800 : (x (-10) 10).toNat ≤ (x (-10) 2).toNat := himp _ _ (hp10 (-10))
      have b6801 := hb (x (-10) 2)
      have b6802 := hb (x (-10) 10)
      clear * - r6800 b6801 b6802 d6791
      omega
    have d6803 : (x (-10) 13).toNat = 0 := by
      have r6804 : (x (-10) 13).toNat ≤ (x (-10) 1).toNat := himp _ _ (hp13 (-10))
      have b6805 := hb (x (-10) 1)
      have b6806 := hb (x (-10) 13)
      clear * - r6804 b6805 b6806 d6779
      omega
    have d6807 : (x (-10) 5).toNat = 0 := by
      have r6808 : (x (-10) 5).toNat ≤ (x (-10) 13).toNat := himp _ _ (hp5 (-10))
      have b6809 := hb (x (-10) 5)
      have b6810 := hb (x (-10) 13)
      clear * - r6808 b6809 b6810 d6803
      omega
    have r6811 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6812 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6813 : (x 5 1).toNat + (x 4 2).toNat + (x 3 3).toNat + (x 2 4).toNat + (x 1 5).toNat + (x 0 6).toNat + (x (-1) 7).toNat + (x (-2) 8).toNat + (x (-3) 9).toNat + (x (-4) 10).toNat + (x (-5) 11).toNat + (x (-6) 12).toNat + (x (-7) 13).toNat + (x (-8) 14).toNat = 3 := by have q := hcount 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6814 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6815 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6816 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6817 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
    have e6818 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
    have e6819 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
    have e6820 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
    have e6821 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
    have e6822 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
    have r6823 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6824 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
    have e6825 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
    have e6826 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
    have e6827 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
    have e6828 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
    have e6829 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
    have r6830 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6831 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
    have e6832 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
    have e6833 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
    have e6834 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
    have e6835 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
    have e6836 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
    have r6837 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6838 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e6839 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e6840 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e6841 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e6842 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e6843 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have r6844 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6845 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
    have e6846 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
    have r6847 : (x 5 2).toNat = (x 5 3).toNat := congrArg Bool.toNat (h23 5)
    have r6848 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e6849 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
    have e6850 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
    have r6851 : 1 ≤ (x 3 5).toNat + (x 2 1 && x 2 6).toNat + (x 1 2 && x 1 7).toNat + (x 0 3 && x 0 8).toNat + (x (-1) 4 && x (-1) 9).toNat + (x (-2) 5 && x (-2) 10).toNat + (x (-3) 6 && x (-3) 11).toNat + (x (-4) 7 && x (-4) 12).toNat + (x (-5) 8 && x (-5) 13).toNat + (x (-6) 9 && x (-6) 14).toNat + (x (-7) 10).toNat := by have q := hcov5 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6852 : 1 ≤ (x 0 6).toNat + (x (-1) 1 && x (-1) 7).toNat + (x (-2) 2 && x (-2) 8).toNat + (x (-3) 3 && x (-3) 9).toNat + (x (-4) 4 && x (-4) 10).toNat + (x (-5) 5 && x (-5) 11).toNat + (x (-6) 6 && x (-6) 12).toNat + (x (-7) 7 && x (-7) 13).toNat + (x (-8) 8 && x (-8) 14).toNat + (x (-9) 9).toNat := by have q := hcov6 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6853 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6854 : 1 ≤ (x (-5) 9).toNat + (x (-6) 1 && x (-6) 10).toNat + (x (-7) 2 && x (-7) 11).toNat + (x (-8) 3 && x (-8) 12).toNat + (x (-9) 4 && x (-9) 13).toNat + (x (-10) 5 && x (-10) 14).toNat + (x (-11) 6).toNat := by have q := hcov9 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6855 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6856 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6857 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6858 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6859 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6860 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := by have q := hcov13 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r6861 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
    have r6862 := hand2 (x (-3) 3) (x (-3) 7)
    have r6863 := hand2 (x (-8) 8) (x (-8) 12)
    have r6864 := hand2 (x (-9) 9) (x (-9) 13)
    have r6865 := hand2 (x 1 2) (x 1 7)
    have r6866 := hand2 (x (-4) 7) (x (-4) 12)
    have r6867 := hand1 (x (-5) 8) (x (-5) 13)
    have r6868 := hand2 (x (-1) 1) (x (-1) 7)
    have r6869 := hand2 (x (-3) 3) (x (-3) 9)
    have r6870 := hand2 (x 1 1) (x 1 7)
    have r6871 := hand1 (x (-5) 7) (x (-5) 13)
    have r6872 := hand2 (x (-7) 2) (x (-7) 11)
    have r6873 := hand1 (x (-9) 4) (x (-9) 13)
    have r6874 := hand1 (x (-5) 4) (x (-5) 13)
    have r6875 := hand2 (x 5 1) (x 5 10)
    have r6876 := hand1 (x 3 3) (x 3 12)
    have r6877 := hand1 (x 1 5) (x 1 14)
    have r6878 := hand2 (x (-9) 1) (x (-9) 11)
    have r6879 := hand2 (x (-11) 3) (x (-11) 13)
    have r6880 := hand1 (x (-12) 4) (x (-12) 14)
    have r6881 := hand2 (x 1 1) (x 1 11)
    have r6882 := hand1 (x (-1) 3) (x (-1) 13)
    have r6883 := hand2 (x (-7) 2) (x (-7) 13)
    have b6884 := hb (x (-15) 7)
    have b6885 := hb (x (-14) 6)
    have b6886 := hb (x (-13) 5)
    have b6887 := hb (x (-12) 4)
    have b6888 := hb (x (-12) 7)
    have b6889 := hb (x (-12) 14)
    have b6890 := hb (x (-11) 6)
    have b6891 := hb (x (-11) 11)
    have b6892 := hb (x (-11) 13)
    have b6893 := hb (x (-10) 5)
    have b6894 := hb (x (-10) 10)
    have b6895 := hb (x (-10) 12)
    have b6896 := hb (x (-10) 14)
    have b6897 := hb (x (-9) 4)
    have b6898 := hb (x (-9) 9)
    have b6899 := hb (x (-9) 11)
    have b6900 := hb (x (-9) 13)
    have b6901 := hb (x (-8) 3)
    have b6902 := hb (x (-8) 7)
    have b6903 := hb (x (-8) 8)
    have b6904 := hb (x (-8) 10)
    have b6905 := hb (x (-8) 11)
    have b6906 := hb (x (-8) 12)
    have b6907 := hb (x (-8) 14)
    have b6908 := hb (x (-7) 2)
    have b6909 := hb (x (-7) 6)
    have b6910 := hb (x (-7) 9)
    have b6911 := hb (x (-7) 10)
    have b6912 := hb (x (-7) 11)
    have b6913 := hb (x (-7) 13)
    have b6914 := hb (x (-7) 14)
    have b6915 := hb (x (-6) 5)
    have b6916 := hb (x (-6) 8)
    have b6917 := hb (x (-6) 9)
    have b6918 := hb (x (-6) 10)
    have b6919 := hb (x (-6) 12)
    have b6920 := hb (x (-6) 13)
    have b6921 := hb (x (-6) 14)
    have b6922 := hb (x (-5) 4)
    have b6923 := hb (x (-5) 7)
    have b6924 := hb (x (-5) 8)
    have b6925 := hb (x (-5) 9)
    have b6926 := hb (x (-5) 11)
    have b6927 := hb (x (-5) 12)
    have b6928 := hb (x (-5) 13)
    have b6929 := hb (x (-4) 6)
    have b6930 := hb (x (-4) 8)
    have b6931 := hb (x (-4) 10)
    have b6932 := hb (x (-4) 11)
    have b6933 := hb (x (-4) 12)
    have b6934 := hb (x (-3) 5)
    have b6935 := hb (x (-3) 7)
    have b6936 := hb (x (-3) 9)
    have b6937 := hb (x (-3) 10)
    have b6938 := hb (x (-3) 11)
    have b6939 := hb (x (-2) 4)
    have b6940 := hb (x (-2) 6)
    have b6941 := hb (x (-2) 8)
    have b6942 := hb (x (-2) 9)
    have b6943 := hb (x (-2) 10)
    have b6944 := hb (x (-1) 3)
    have b6945 := hb (x (-1) 5)
    have b6946 := hb (x (-1) 7)
    have b6947 := hb (x (-1) 8)
    have b6948 := hb (x (-1) 9)
    have b6949 := hb (x 0 2)
    have b6950 := hb (x 0 4)
    have b6951 := hb (x 0 6)
    have b6952 := hb (x 0 7)
    have b6953 := hb (x 0 8)
    have b6954 := hb (x 1 1)
    have b6955 := hb (x 1 3)
    have b6956 := hb (x 1 5)
    have b6957 := hb (x 1 6)
    have b6958 := hb (x 1 7)
    have b6959 := hb (x 1 11)
    have b6960 := hb (x 2 2)
    have b6961 := hb (x 2 4)
    have b6962 := hb (x 2 5)
    have b6963 := hb (x 2 6)
    have b6964 := hb (x 2 10)
    have b6965 := hb (x 3 1)
    have b6966 := hb (x 3 3)
    have b6967 := hb (x 3 4)
    have b6968 := hb (x 3 5)
    have b6969 := hb (x 4 2)
    have b6970 := hb (x 4 3)
    have b6971 := hb (x 4 4)
    have b6972 := hb (x 4 11)
    have b6973 := hb (x 5 1)
    have b6974 := hb (x 5 2)
    have b6975 := hb (x 5 3)
    have b6976 := hb (x 5 10)
    have b6977 := hb (x 6 1)
    have b6978 := hb (x 6 2)
    have b6979 := hb (x 6 9)
    have b6980 := hb (x 7 1)
    have b6981 := hb (x 7 8)
    have b6982 := hb (x (-2) 2 && x (-2) 6)
    have b6983 := hb (x (-3) 3 && x (-3) 7)
    have b6984 := hb (x (-4) 4 && x (-4) 8)
    have b6985 := hb (x (-5) 5 && x (-5) 9)
    have b6986 := hb (x (-6) 6 && x (-6) 10)
    have b6987 := hb (x (-7) 7 && x (-7) 11)
    have b6988 := hb (x (-8) 8 && x (-8) 12)
    have b6989 := hb (x (-9) 9 && x (-9) 13)
    have b6990 := hb (x 2 1 && x 2 6)
    have b6991 := hb (x 1 2 && x 1 7)
    have b6992 := hb (x 0 3 && x 0 8)
    have b6993 := hb (x (-1) 4 && x (-1) 9)
    have b6994 := hb (x (-2) 5 && x (-2) 10)
    have b6995 := hb (x (-3) 6 && x (-3) 11)
    have b6996 := hb (x (-4) 7 && x (-4) 12)
    have b6997 := hb (x (-5) 8 && x (-5) 13)
    have b6998 := hb (x (-6) 9 && x (-6) 14)
    have b6999 := hb (x (-1) 1 && x (-1) 7)
    have b7000 := hb (x (-2) 2 && x (-2) 8)
    have b7001 := hb (x (-3) 3 && x (-3) 9)
    have b7002 := hb (x (-4) 4 && x (-4) 10)
    have b7003 := hb (x (-5) 5 && x (-5) 11)
    have b7004 := hb (x (-6) 6 && x (-6) 12)
    have b7005 := hb (x (-7) 7 && x (-7) 13)
    have b7006 := hb (x (-8) 8 && x (-8) 14)
    have b7007 := hb (x 1 1 && x 1 7)
    have b7008 := hb (x 0 2 && x 0 8)
    have b7009 := hb (x (-1) 3 && x (-1) 9)
    have b7010 := hb (x (-2) 4 && x (-2) 10)
    have b7011 := hb (x (-3) 5 && x (-3) 11)
    have b7012 := hb (x (-4) 6 && x (-4) 12)
    have b7013 := hb (x (-5) 7 && x (-5) 13)
    have b7014 := hb (x (-6) 8 && x (-6) 14)
    have b7015 := hb (x (-6) 1 && x (-6) 10)
    have b7016 := hb (x (-7) 2 && x (-7) 11)
    have b7017 := hb (x (-8) 3 && x (-8) 12)
    have b7018 := hb (x (-9) 4 && x (-9) 13)
    have b7019 := hb (x (-10) 5 && x (-10) 14)
    have b7020 := hb (x (-2) 1 && x (-2) 10)
    have b7021 := hb (x (-3) 2 && x (-3) 11)
    have b7022 := hb (x (-4) 3 && x (-4) 12)
    have b7023 := hb (x (-5) 4 && x (-5) 13)
    have b7024 := hb (x (-6) 5 && x (-6) 14)
    have b7025 := hb (x 5 1 && x 5 10)
    have b7026 := hb (x 4 2 && x 4 11)
    have b7027 := hb (x 3 3 && x 3 12)
    have b7028 := hb (x 2 4 && x 2 13)
    have b7029 := hb (x 1 5 && x 1 14)
    have b7030 := hb (x (-9) 1 && x (-9) 11)
    have b7031 := hb (x (-10) 2 && x (-10) 12)
    have b7032 := hb (x (-11) 3 && x (-11) 13)
    have b7033 := hb (x (-12) 4 && x (-12) 14)
    have b7034 := hb (x 1 1 && x 1 11)
    have b7035 := hb (x 0 2 && x 0 12)
    have b7036 := hb (x (-1) 3 && x (-1) 13)
    have b7037 := hb (x (-2) 4 && x (-2) 14)
    have b7038 := hb (x (-6) 1 && x (-6) 12)
    have b7039 := hb (x (-7) 2 && x (-7) 13)
    have b7040 := hb (x (-8) 3 && x (-8) 14)
    have b7041 := hb (x (-6) 1 && x (-6) 14)
    linarith only [r6811, r6812, r6813, r6814, r6815, r6816, e6817, e6818, e6819, e6820, e6821, e6822, r6823, e6824, e6825, e6826, e6827, e6828, e6829, r6830, e6831, e6832, e6833, e6834, e6835, e6836, r6837, e6838, e6839, e6840, e6841, e6842, e6843, r6844, e6845, e6846, r6847, r6848, e6849, e6850, r6851, r6852, r6853, r6854, r6855, r6856, r6857, r6858, r6859, r6860, r6861, r6862, r6863, r6864, r6865, r6866, r6867, r6868, r6869, r6870, r6871, r6872, r6873, r6874, r6875, r6876, r6877, r6878, r6879, r6880, r6881, r6882, r6883, b6884, b6885, b6886, b6887, b6888, b6889, b6890, b6891, b6892, b6893, b6894, b6895, b6896, b6897, b6898, b6899, b6900, b6901, b6902, b6903, b6904, b6905, b6906, b6907, b6908, b6909, b6910, b6911, b6912, b6913, b6914, b6915, b6916, b6917, b6918, b6919, b6920, b6921, b6922, b6923, b6924, b6925, b6926, b6927, b6928, b6929, b6930, b6931, b6932, b6933, b6934, b6935, b6936, b6937, b6938, b6939, b6940, b6941, b6942, b6943, b6944, b6945, b6946, b6947, b6948, b6949, b6950, b6951, b6952, b6953, b6954, b6955, b6956, b6957, b6958, b6959, b6960, b6961, b6962, b6963, b6964, b6965, b6966, b6967, b6968, b6969, b6970, b6971, b6972, b6973, b6974, b6975, b6976, b6977, b6978, b6979, b6980, b6981, b6982, b6983, b6984, b6985, b6986, b6987, b6988, b6989, b6990, b6991, b6992, b6993, b6994, b6995, b6996, b6997, b6998, b6999, b7000, b7001, b7002, b7003, b7004, b7005, b7006, b7007, b7008, b7009, b7010, b7011, b7012, b7013, b7014, b7015, b7016, b7017, b7018, b7019, b7020, b7021, b7022, b7023, b7024, b7025, b7026, b7027, b7028, b7029, b7030, b7031, b7032, b7033, b7034, b7035, b7036, b7037, b7038, b7039, b7040, b7041, d6807, d6799, d6783, d6755, d6767, d6763, d6739, d6731, d6719, d6723, d6711, d6715, d6691, d6639, d6663, d6659, d6293, d6603, d6619, d6265, d6241, d6455, d6451, g0, d6479, d6575, d6503, d6571, d6579, d6511, d6555, d6563, d6567, d6527, d6535, d6551, d6539, d6547, d6607, d6353, d6385, d6413, d6441, d6491, d6471, d6261, d6289, d6321, d6703, d6615, d6349, d6381, d6409, d6437, d6747, d6463, d6257, d6285, d6317, d6643, d6699, d6687, d6759, d6787, d6281, d6313, d6655, d6695, d6559, d6499, d6795, d6459, d6599, d6683, d6743, d6679]
  · have f7042 : (x 0 1).toNat = 1 := by rw [h6445]; rfl
    have d7043 : (x 0 14).toNat = 1 := by
      have r7044 : (x 0 1).toNat = (x 0 14).toNat := congrArg Bool.toNat (h114 0)
      have b7045 := hb (x 0 1)
      have b7046 := hb (x 0 14)
      clear * - r7044 b7045 b7046 f7042
      omega
    have d7047 : (x 1 14).toNat = 0 := by
      have r7048 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7049 := hb (x 0 1)
      have b7050 := hb (x 1 14)
      clear * - r7048 b7049 b7050 f7042
      omega
    have d7051 : (x 1 1 && x 1 14).toNat = 0 := by
      have r7052 := hand2 (x 1 1) (x 1 14)
      have b7053 := hb (x 1 14)
      have b7054 := hb (x 1 1 && x 1 14)
      clear * - r7052 b7053 b7054 d7047
      omega
    have d7055 : (x 1 3 && x 1 14).toNat = 0 := by
      have r7056 := hand2 (x 1 3) (x 1 14)
      have b7057 := hb (x 1 14)
      have b7058 := hb (x 1 3 && x 1 14)
      clear * - r7056 b7057 b7058 d7047
      omega
    have d7059 : (x 1 1).toNat = 0 := by
      have r7060 : (x 1 1).toNat = (x 1 14).toNat := congrArg Bool.toNat (h114 1)
      have b7061 := hb (x 1 1)
      have b7062 := hb (x 1 14)
      clear * - r7060 b7061 b7062 d7047
      omega
    have d7063 : (x 1 1 && x 1 12).toNat = 0 := by
      have r7064 := hand1 (x 1 1) (x 1 12)
      have b7065 := hb (x 1 1)
      have b7066 := hb (x 1 1 && x 1 12)
      clear * - r7064 b7065 b7066 d7059
      omega
    have d7067 : (x 1 1 && x 1 7).toNat = 0 := by
      have r7068 := hand1 (x 1 1) (x 1 7)
      have b7069 := hb (x 1 1)
      have b7070 := hb (x 1 1 && x 1 7)
      clear * - r7068 b7069 b7070 d7059
      omega
    have d7071 : (x 1 13).toNat = 0 := by
      have r7072 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
      have b7073 := hb (x 1 1)
      have b7074 := hb (x 1 13)
      clear * - r7072 b7073 b7074 d7059
      omega
    have d7075 : (x 1 3 && x 1 13).toNat = 0 := by
      have r7076 := hand2 (x 1 3) (x 1 13)
      have b7077 := hb (x 1 13)
      have b7078 := hb (x 1 3 && x 1 13)
      clear * - r7076 b7077 b7078 d7071
      omega
    have d7079 : (x 1 5).toNat = 0 := by
      have r7080 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
      have b7081 := hb (x 1 5)
      have b7082 := hb (x 1 13)
      clear * - r7080 b7081 b7082 d7071
      omega
    have d7083 : (x 1 5 && x 1 10).toNat = 0 := by
      have r7084 := hand1 (x 1 5) (x 1 10)
      have b7085 := hb (x 1 5)
      have b7086 := hb (x 1 5 && x 1 10)
      clear * - r7084 b7085 b7086 d7079
      omega
    have d7087 : (x 2 14).toNat = 1 := by
      have r7088 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7089 := hb (x 1 1)
      have b7090 := hb (x 2 14)
      clear * - r7088 b7089 b7090 d7059
      omega
    have d7091 : (x 2 1).toNat = 1 := by
      have r7092 : (x 2 1).toNat = (x 2 14).toNat := congrArg Bool.toNat (h114 2)
      have b7093 := hb (x 2 1)
      have b7094 := hb (x 2 14)
      clear * - r7092 b7093 b7094 d7087
      omega
    have d7095 : (x 3 14).toNat = 0 := by
      have r7096 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7097 := hb (x 2 1)
      have b7098 := hb (x 3 14)
      clear * - r7096 b7097 b7098 d7091
      omega
    have d7099 : (x 3 3 && x 3 14).toNat = 0 := by
      have r7100 := hand2 (x 3 3) (x 3 14)
      have b7101 := hb (x 3 14)
      have b7102 := hb (x 3 3 && x 3 14)
      clear * - r7100 b7101 b7102 d7095
      omega
    have d7103 : (x 3 1).toNat = 0 := by
      have r7104 : (x 3 1).toNat = (x 3 14).toNat := congrArg Bool.toNat (h114 3)
      have b7105 := hb (x 3 1)
      have b7106 := hb (x 3 14)
      clear * - r7104 b7105 b7106 d7095
      omega
    have d7107 : (x 3 1 && x 3 12).toNat = 0 := by
      have r7108 := hand1 (x 3 1) (x 3 12)
      have b7109 := hb (x 3 1)
      have b7110 := hb (x 3 1 && x 3 12)
      clear * - r7108 b7109 b7110 d7103
      omega
    have d7111 : (x 3 1 && x 3 11).toNat = 0 := by
      have r7112 := hand1 (x 3 1) (x 3 11)
      have b7113 := hb (x 3 1)
      have b7114 := hb (x 3 1 && x 3 11)
      clear * - r7112 b7113 b7114 d7103
      omega
    have d7115 : (x 3 13).toNat = 0 := by
      have r7116 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b7117 := hb (x 3 1)
      have b7118 := hb (x 3 13)
      clear * - r7116 b7117 b7118 d7103
      omega
    have d7119 : (x 3 5).toNat = 0 := by
      have r7120 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
      have b7121 := hb (x 3 5)
      have b7122 := hb (x 3 13)
      clear * - r7120 b7121 b7122 d7115
      omega
    have d7123 : (x 4 14).toNat = 1 := by
      have r7124 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7125 := hb (x 3 1)
      have b7126 := hb (x 4 14)
      clear * - r7124 b7125 b7126 d7103
      omega
    have d7127 : (x 4 1).toNat = 1 := by
      have r7128 : (x 4 1).toNat = (x 4 14).toNat := congrArg Bool.toNat (h114 4)
      have b7129 := hb (x 4 1)
      have b7130 := hb (x 4 14)
      clear * - r7128 b7129 b7130 d7123
      omega
    have d7131 : (x 5 14).toNat = 0 := by
      have r7132 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7133 := hb (x 4 1)
      have b7134 := hb (x 5 14)
      clear * - r7132 b7133 b7134 d7127
      omega
    have d7135 : (x 5 3 && x 5 14).toNat = 0 := by
      have r7136 := hand2 (x 5 3) (x 5 14)
      have b7137 := hb (x 5 14)
      have b7138 := hb (x 5 3 && x 5 14)
      clear * - r7136 b7137 b7138 d7131
      omega
    have d7139 : (x 5 4 && x 5 14).toNat = 0 := by
      have r7140 := hand2 (x 5 4) (x 5 14)
      have b7141 := hb (x 5 14)
      have b7142 := hb (x 5 4 && x 5 14)
      clear * - r7140 b7141 b7142 d7131
      omega
    have d7143 : (x 5 1).toNat = 0 := by
      have r7144 : (x 5 1).toNat = (x 5 14).toNat := congrArg Bool.toNat (h114 5)
      have b7145 := hb (x 5 1)
      have b7146 := hb (x 5 14)
      clear * - r7144 b7145 b7146 d7131
      omega
    have d7147 : (x 5 1 && x 5 12).toNat = 0 := by
      have r7148 := hand1 (x 5 1) (x 5 12)
      have b7149 := hb (x 5 1)
      have b7150 := hb (x 5 1 && x 5 12)
      clear * - r7148 b7149 b7150 d7143
      omega
    have d7151 : (x 5 1 && x 5 6).toNat = 0 := by
      have r7152 := hand1 (x 5 1) (x 5 6)
      have b7153 := hb (x 5 1)
      have b7154 := hb (x 5 1 && x 5 6)
      clear * - r7152 b7153 b7154 d7143
      omega
    have d7155 : (x 5 9).toNat = 0 := by
      have r7156 : (x 5 9).toNat ≤ (x 5 1).toNat := himp _ _ (hp9 5)
      have b7157 := hb (x 5 1)
      have b7158 := hb (x 5 9)
      clear * - r7156 b7157 b7158 d7143
      omega
    have d7159 : (x 6 14).toNat = 1 := by
      have r7160 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7161 := hb (x 5 1)
      have b7162 := hb (x 6 14)
      clear * - r7160 b7161 b7162 d7143
      omega
    have d7163 : (x 6 1).toNat = 1 := by
      have r7164 : (x 6 1).toNat = (x 6 14).toNat := congrArg Bool.toNat (h114 6)
      have b7165 := hb (x 6 1)
      have b7166 := hb (x 6 14)
      clear * - r7164 b7165 b7166 d7159
      omega
    have d7167 : (x 7 14).toNat = 0 := by
      have r7168 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7169 := hb (x 6 1)
      have b7170 := hb (x 7 14)
      clear * - r7168 b7169 b7170 d7163
      omega
    have d7171 : (x 7 1).toNat = 0 := by
      have r7172 : (x 7 1).toNat = (x 7 14).toNat := congrArg Bool.toNat (h114 7)
      have b7173 := hb (x 7 1)
      have b7174 := hb (x 7 14)
      clear * - r7172 b7173 b7174 d7167
      omega
    have d7175 : (x 7 1 && x 7 12).toNat = 0 := by
      have r7176 := hand1 (x 7 1) (x 7 12)
      have b7177 := hb (x 7 1)
      have b7178 := hb (x 7 1 && x 7 12)
      clear * - r7176 b7177 b7178 d7171
      omega
    have d7179 : (x 8 14).toNat = 1 := by
      have r7180 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7181 := hb (x 7 1)
      have b7182 := hb (x 8 14)
      clear * - r7180 b7181 b7182 d7171
      omega
    have d7183 : (x 8 1).toNat = 1 := by
      have r7184 : (x 8 1).toNat = (x 8 14).toNat := congrArg Bool.toNat (h114 8)
      have b7185 := hb (x 8 1)
      have b7186 := hb (x 8 14)
      clear * - r7184 b7185 b7186 d7179
      omega
    have d7187 : (x 9 14).toNat = 0 := by
      have r7188 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7189 := hb (x 8 1)
      have b7190 := hb (x 9 14)
      clear * - r7188 b7189 b7190 d7183
      omega
    have d7191 : (x 9 1).toNat = 0 := by
      have r7192 : (x 9 1).toNat = (x 9 14).toNat := congrArg Bool.toNat (h114 9)
      have b7193 := hb (x 9 1)
      have b7194 := hb (x 9 14)
      clear * - r7192 b7193 b7194 d7187
      omega
    have d7195 : (x 10 14).toNat = 1 := by
      have r7196 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7197 := hb (x 9 1)
      have b7198 := hb (x 10 14)
      clear * - r7196 b7197 b7198 d7191
      omega
    have d7199 : (x 10 1).toNat = 1 := by
      have r7200 : (x 10 1).toNat = (x 10 14).toNat := congrArg Bool.toNat (h114 10)
      have b7201 := hb (x 10 1)
      have b7202 := hb (x 10 14)
      clear * - r7200 b7201 b7202 d7195
      omega
    have d7203 : (x 9 2).toNat = 0 := by
      have r7204 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
      have b7205 := hb (x 9 2)
      have b7206 := hb (x 9 14)
      clear * - r7204 b7205 b7206 d7187
      omega
    have d7207 : (x 9 10).toNat = 0 := by
      have r7208 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
      have b7209 := hb (x 9 2)
      have b7210 := hb (x 9 10)
      clear * - r7208 b7209 b7210 d7203
      omega
    have d7211 : (x 7 2).toNat = 0 := by
      have r7212 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
      have b7213 := hb (x 7 2)
      have b7214 := hb (x 7 14)
      clear * - r7212 b7213 b7214 d7167
      omega
    have d7215 : (x 7 2 && x 7 12).toNat = 0 := by
      have r7216 := hand1 (x 7 2) (x 7 12)
      have b7217 := hb (x 7 2)
      have b7218 := hb (x 7 2 && x 7 12)
      clear * - r7216 b7217 b7218 d7211
      omega
    have d7219 : (x 5 6).toNat = 0 := by
      have r7220 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
      have b7221 := hb (x 5 6)
      have b7222 := hb (x 5 14)
      clear * - r7220 b7221 b7222 d7131
      omega
    have d7223 : (x 5 2 && x 5 6).toNat = 0 := by
      have r7224 := hand2 (x 5 2) (x 5 6)
      have b7225 := hb (x 5 6)
      have b7226 := hb (x 5 2 && x 5 6)
      clear * - r7224 b7225 b7226 d7219
      omega
    have d7227 : (x 5 2).toNat = 0 := by
      have r7228 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
      have b7229 := hb (x 5 2)
      have b7230 := hb (x 5 14)
      clear * - r7228 b7229 b7230 d7131
      omega
    have d7231 : (x 5 3).toNat = 0 := by
      have r7232 : (x 5 2).toNat = (x 5 3).toNat := congrArg Bool.toNat (h23 5)
      have b7233 := hb (x 5 2)
      have b7234 := hb (x 5 3)
      clear * - r7232 b7233 b7234 d7227
      omega
    have d7235 : (x 5 10).toNat = 0 := by
      have r7236 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
      have b7237 := hb (x 5 2)
      have b7238 := hb (x 5 10)
      clear * - r7236 b7237 b7238 d7227
      omega
    have d7239 : (x 3 6).toNat = 0 := by
      have r7240 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
      have b7241 := hb (x 3 6)
      have b7242 := hb (x 3 14)
      clear * - r7240 b7241 b7242 d7095
      omega
    have d7243 : (x 3 2).toNat = 0 := by
      have r7244 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b7245 := hb (x 3 2)
      have b7246 := hb (x 3 14)
      clear * - r7244 b7245 b7246 d7095
      omega
    have d7247 : (x 3 3).toNat = 0 := by
      have r7248 : (x 3 2).toNat = (x 3 3).toNat := congrArg Bool.toNat (h23 3)
      have b7249 := hb (x 3 2)
      have b7250 := hb (x 3 3)
      clear * - r7248 b7249 b7250 d7243
      omega
    have d7251 : (x 3 3 && x 3 8).toNat = 0 := by
      have r7252 := hand1 (x 3 3) (x 3 8)
      have b7253 := hb (x 3 3)
      have b7254 := hb (x 3 3 && x 3 8)
      clear * - r7252 b7253 b7254 d7247
      omega
    have d7255 : (x 3 11).toNat = 0 := by
      have r7256 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b7257 := hb (x 3 3)
      have b7258 := hb (x 3 11)
      clear * - r7256 b7257 b7258 d7247
      omega
    have d7259 : (x 1 6).toNat = 0 := by
      have r7260 : (x 1 6).toNat ≤ (x 1 14).toNat := himp _ _ (hp6 1)
      have b7261 := hb (x 1 6)
      have b7262 := hb (x 1 14)
      clear * - r7260 b7261 b7262 d7047
      omega
    have d7263 : (x 1 6 && x 1 10).toNat = 0 := by
      have r7264 := hand1 (x 1 6) (x 1 10)
      have b7265 := hb (x 1 6)
      have b7266 := hb (x 1 6 && x 1 10)
      clear * - r7264 b7265 b7266 d7259
      omega
    have d7267 : (x 1 2).toNat = 0 := by
      have r7268 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
      have b7269 := hb (x 1 2)
      have b7270 := hb (x 1 14)
      clear * - r7268 b7269 b7270 d7047
      omega
    have d7271 : (x 1 2 && x 1 8).toNat = 0 := by
      have r7272 := hand1 (x 1 2) (x 1 8)
      have b7273 := hb (x 1 2)
      have b7274 := hb (x 1 2 && x 1 8)
      clear * - r7272 b7273 b7274 d7267
      omega
    have d7275 : (x 1 2 && x 1 7).toNat = 0 := by
      have r7276 := hand1 (x 1 2) (x 1 7)
      have b7277 := hb (x 1 2)
      have b7278 := hb (x 1 2 && x 1 7)
      clear * - r7276 b7277 b7278 d7267
      omega
    have d7279 : (x 1 3).toNat = 0 := by
      have r7280 : (x 1 2).toNat = (x 1 3).toNat := congrArg Bool.toNat (h23 1)
      have b7281 := hb (x 1 2)
      have b7282 := hb (x 1 3)
      clear * - r7280 b7281 b7282 d7267
      omega
    have d7283 : (x 1 10).toNat = 0 := by
      have r7284 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
      have b7285 := hb (x 1 2)
      have b7286 := hb (x 1 10)
      clear * - r7284 b7285 b7286 d7267
      omega
    have d7287 : (x (-1) 1).toNat = 0 := by
      have r7288 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7289 := hb (x (-1) 1)
      have b7290 := hb (x 0 14)
      clear * - r7288 b7289 b7290 d7043
      omega
    have d7291 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
      have r7292 := hand1 (x (-1) 1) (x (-1) 12)
      have b7293 := hb (x (-1) 1)
      have b7294 := hb (x (-1) 1 && x (-1) 12)
      clear * - r7292 b7293 b7294 d7287
      omega
    have d7295 : (x (-1) 1 && x (-1) 10).toNat = 0 := by
      have r7296 := hand1 (x (-1) 1) (x (-1) 10)
      have b7297 := hb (x (-1) 1)
      have b7298 := hb (x (-1) 1 && x (-1) 10)
      clear * - r7296 b7297 b7298 d7287
      omega
    have d7299 : (x (-1) 1 && x (-1) 8).toNat = 0 := by
      have r7300 := hand1 (x (-1) 1) (x (-1) 8)
      have b7301 := hb (x (-1) 1)
      have b7302 := hb (x (-1) 1 && x (-1) 8)
      clear * - r7300 b7301 b7302 d7287
      omega
    have d7303 : (x (-1) 14).toNat = 0 := by
      have r7304 : (x (-1) 1).toNat = (x (-1) 14).toNat := congrArg Bool.toNat (h114 (-1))
      have b7305 := hb (x (-1) 1)
      have b7306 := hb (x (-1) 14)
      clear * - r7304 b7305 b7306 d7287
      omega
    have d7307 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
      have r7308 := hand2 (x (-1) 3) (x (-1) 14)
      have b7309 := hb (x (-1) 14)
      have b7310 := hb (x (-1) 3 && x (-1) 14)
      clear * - r7308 b7309 b7310 d7303
      omega
    have d7311 : (x (-1) 2).toNat = 0 := by
      have r7312 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
      have b7313 := hb (x (-1) 2)
      have b7314 := hb (x (-1) 14)
      clear * - r7312 b7313 b7314 d7303
      omega
    have d7315 : (x (-1) 3).toNat = 0 := by
      have r7316 : (x (-1) 2).toNat = (x (-1) 3).toNat := congrArg Bool.toNat (h23 (-1))
      have b7317 := hb (x (-1) 2)
      have b7318 := hb (x (-1) 3)
      clear * - r7316 b7317 b7318 d7311
      omega
    have d7319 : (x (-1) 10).toNat = 0 := by
      have r7320 : (x (-1) 10).toNat ≤ (x (-1) 2).toNat := himp _ _ (hp10 (-1))
      have b7321 := hb (x (-1) 2)
      have b7322 := hb (x (-1) 10)
      clear * - r7320 b7321 b7322 d7311
      omega
    have d7323 : (x (-1) 4 && x (-1) 10).toNat = 0 := by
      have r7324 := hand2 (x (-1) 4) (x (-1) 10)
      have b7325 := hb (x (-1) 10)
      have b7326 := hb (x (-1) 4 && x (-1) 10)
      clear * - r7324 b7325 b7326 d7319
      omega
    have d7327 : (x (-1) 13).toNat = 0 := by
      have r7328 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
      have b7329 := hb (x (-1) 1)
      have b7330 := hb (x (-1) 13)
      clear * - r7328 b7329 b7330 d7287
      omega
    have d7331 : (x (-1) 5).toNat = 0 := by
      have r7332 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
      have b7333 := hb (x (-1) 5)
      have b7334 := hb (x (-1) 13)
      clear * - r7332 b7333 b7334 d7327
      omega
    have d7335 : (x (-2) 1).toNat = 1 := by
      have r7336 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7337 := hb (x (-2) 1)
      have b7338 := hb (x (-1) 14)
      clear * - r7336 b7337 b7338 d7303
      omega
    have d7339 : (x (-2) 14).toNat = 1 := by
      have r7340 : (x (-2) 1).toNat = (x (-2) 14).toNat := congrArg Bool.toNat (h114 (-2))
      have b7341 := hb (x (-2) 1)
      have b7342 := hb (x (-2) 14)
      clear * - r7340 b7341 b7342 d7335
      omega
    have d7343 : (x (-3) 1).toNat = 0 := by
      have r7344 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7345 := hb (x (-3) 1)
      have b7346 := hb (x (-2) 14)
      clear * - r7344 b7345 b7346 d7339
      omega
    have d7347 : (x (-3) 14).toNat = 0 := by
      have r7348 : (x (-3) 1).toNat = (x (-3) 14).toNat := congrArg Bool.toNat (h114 (-3))
      have b7349 := hb (x (-3) 1)
      have b7350 := hb (x (-3) 14)
      clear * - r7348 b7349 b7350 d7343
      omega
    have d7351 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
      have r7352 := hand2 (x (-3) 3) (x (-3) 14)
      have b7353 := hb (x (-3) 14)
      have b7354 := hb (x (-3) 3 && x (-3) 14)
      clear * - r7352 b7353 b7354 d7347
      omega
    have d7355 : (x (-3) 9 && x (-3) 14).toNat = 0 := by
      have r7356 := hand2 (x (-3) 9) (x (-3) 14)
      have b7357 := hb (x (-3) 14)
      have b7358 := hb (x (-3) 9 && x (-3) 14)
      clear * - r7356 b7357 b7358 d7347
      omega
    have d7359 : (x (-3) 6).toNat = 0 := by
      have r7360 : (x (-3) 6).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp6 (-3))
      have b7361 := hb (x (-3) 6)
      have b7362 := hb (x (-3) 14)
      clear * - r7360 b7361 b7362 d7347
      omega
    have d7363 : (x (-3) 6 && x (-3) 12).toNat = 0 := by
      have r7364 := hand1 (x (-3) 6) (x (-3) 12)
      have b7365 := hb (x (-3) 6)
      have b7366 := hb (x (-3) 6 && x (-3) 12)
      clear * - r7364 b7365 b7366 d7359
      omega
    have d7367 : (x (-3) 2).toNat = 0 := by
      have r7368 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b7369 := hb (x (-3) 2)
      have b7370 := hb (x (-3) 14)
      clear * - r7368 b7369 b7370 d7347
      omega
    have d7371 : (x (-3) 3).toNat = 0 := by
      have r7372 : (x (-3) 2).toNat = (x (-3) 3).toNat := congrArg Bool.toNat (h23 (-3))
      have b7373 := hb (x (-3) 2)
      have b7374 := hb (x (-3) 3)
      clear * - r7372 b7373 b7374 d7367
      omega
    have d7375 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
      have r7376 := hand1 (x (-3) 3) (x (-3) 12)
      have b7377 := hb (x (-3) 3)
      have b7378 := hb (x (-3) 3 && x (-3) 12)
      clear * - r7376 b7377 b7378 d7371
      omega
    have d7379 : (x (-3) 3 && x (-3) 10).toNat = 0 := by
      have r7380 := hand1 (x (-3) 3) (x (-3) 10)
      have b7381 := hb (x (-3) 3)
      have b7382 := hb (x (-3) 3 && x (-3) 10)
      clear * - r7380 b7381 b7382 d7371
      omega
    have d7383 : (x (-3) 3 && x (-3) 7).toNat = 0 := by
      have r7384 := hand1 (x (-3) 3) (x (-3) 7)
      have b7385 := hb (x (-3) 3)
      have b7386 := hb (x (-3) 3 && x (-3) 7)
      clear * - r7384 b7385 b7386 d7371
      omega
    have d7387 : (x (-3) 10).toNat = 0 := by
      have r7388 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
      have b7389 := hb (x (-3) 2)
      have b7390 := hb (x (-3) 10)
      clear * - r7388 b7389 b7390 d7367
      omega
    have d7391 : (x (-3) 13).toNat = 0 := by
      have r7392 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
      have b7393 := hb (x (-3) 1)
      have b7394 := hb (x (-3) 13)
      clear * - r7392 b7393 b7394 d7343
      omega
    have d7395 : (x (-3) 9).toNat = 0 := by
      have r7396 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
      have b7397 := hb (x (-3) 1)
      have b7398 := hb (x (-3) 9)
      clear * - r7396 b7397 b7398 d7343
      omega
    have d7399 : (x (-4) 1).toNat = 1 := by
      have r7400 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7401 := hb (x (-4) 1)
      have b7402 := hb (x (-3) 14)
      clear * - r7400 b7401 b7402 d7347
      omega
    have d7403 : (x (-4) 14).toNat = 1 := by
      have r7404 : (x (-4) 1).toNat = (x (-4) 14).toNat := congrArg Bool.toNat (h114 (-4))
      have b7405 := hb (x (-4) 1)
      have b7406 := hb (x (-4) 14)
      clear * - r7404 b7405 b7406 d7399
      omega
    have d7407 : (x (-5) 1).toNat = 0 := by
      have r7408 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := by have q := hd14 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7409 := hb (x (-5) 1)
      have b7410 := hb (x (-4) 14)
      clear * - r7408 b7409 b7410 d7403
      omega
    have d7411 : (x (-5) 1 && x (-5) 14).toNat = 0 := by
      have r7412 := hand1 (x (-5) 1) (x (-5) 14)
      have b7413 := hb (x (-5) 1)
      have b7414 := hb (x (-5) 1 && x (-5) 14)
      clear * - r7412 b7413 b7414 d7407
      omega
    have d7415 : (x (-5) 14).toNat = 0 := by
      have r7416 : (x (-5) 1).toNat = (x (-5) 14).toNat := congrArg Bool.toNat (h114 (-5))
      have b7417 := hb (x (-5) 1)
      have b7418 := hb (x (-5) 14)
      clear * - r7416 b7417 b7418 d7407
      omega
    have d7419 : (x (-5) 8 && x (-5) 14).toNat = 0 := by
      have r7420 := hand2 (x (-5) 8) (x (-5) 14)
      have b7421 := hb (x (-5) 14)
      have b7422 := hb (x (-5) 8 && x (-5) 14)
      clear * - r7420 b7421 b7422 d7415
      omega
    have d7423 : (x (-5) 6).toNat = 0 := by
      have r7424 : (x (-5) 6).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp6 (-5))
      have b7425 := hb (x (-5) 6)
      have b7426 := hb (x (-5) 14)
      clear * - r7424 b7425 b7426 d7415
      omega
    have d7427 : (x (-5) 2).toNat = 0 := by
      have r7428 : (x (-5) 2).toNat ≤ (x (-5) 14).toNat := himp _ _ (hp2 (-5))
      have b7429 := hb (x (-5) 2)
      have b7430 := hb (x (-5) 14)
      clear * - r7428 b7429 b7430 d7415
      omega
    have d7431 : (x (-5) 3).toNat = 0 := by
      have r7432 : (x (-5) 2).toNat = (x (-5) 3).toNat := congrArg Bool.toNat (h23 (-5))
      have b7433 := hb (x (-5) 2)
      have b7434 := hb (x (-5) 3)
      clear * - r7432 b7433 b7434 d7427
      omega
    have d7435 : (x (-5) 3 && x (-5) 13).toNat = 0 := by
      have r7436 := hand1 (x (-5) 3) (x (-5) 13)
      have b7437 := hb (x (-5) 3)
      have b7438 := hb (x (-5) 3 && x (-5) 13)
      clear * - r7436 b7437 b7438 d7431
      omega
    have d7439 : (x (-5) 11).toNat = 0 := by
      have r7440 : (x (-5) 11).toNat ≤ (x (-5) 3).toNat := himp _ _ (hp11 (-5))
      have b7441 := hb (x (-5) 3)
      have b7442 := hb (x (-5) 11)
      clear * - r7440 b7441 b7442 d7431
      omega
    have d7443 : (x (-5) 13).toNat = 0 := by
      have r7444 : (x (-5) 13).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp13 (-5))
      have b7445 := hb (x (-5) 1)
      have b7446 := hb (x (-5) 13)
      clear * - r7444 b7445 b7446 d7407
      omega
    have d7447 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
      have r7448 := hand2 (x (-5) 4) (x (-5) 13)
      have b7449 := hb (x (-5) 13)
      have b7450 := hb (x (-5) 4 && x (-5) 13)
      clear * - r7448 b7449 b7450 d7443
      omega
    have d7451 : (x (-5) 7 && x (-5) 13).toNat = 0 := by
      have r7452 := hand2 (x (-5) 7) (x (-5) 13)
      have b7453 := hb (x (-5) 13)
      have b7454 := hb (x (-5) 7 && x (-5) 13)
      clear * - r7452 b7453 b7454 d7443
      omega
    have d7455 : (x (-5) 8 && x (-5) 13).toNat = 0 := by
      have r7456 := hand2 (x (-5) 8) (x (-5) 13)
      have b7457 := hb (x (-5) 13)
      have b7458 := hb (x (-5) 8 && x (-5) 13)
      clear * - r7456 b7457 b7458 d7443
      omega
    have d7459 : (x (-5) 9).toNat = 0 := by
      have r7460 : (x (-5) 9).toNat ≤ (x (-5) 1).toNat := himp _ _ (hp9 (-5))
      have b7461 := hb (x (-5) 1)
      have b7462 := hb (x (-5) 9)
      clear * - r7460 b7461 b7462 d7407
      omega
    have d7463 : (x (-6) 1).toNat = 1 := by
      have r7464 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := by have q := hd14 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7465 := hb (x (-6) 1)
      have b7466 := hb (x (-5) 14)
      clear * - r7464 b7465 b7466 d7415
      omega
    have d7467 : (x (-6) 14).toNat = 1 := by
      have r7468 : (x (-6) 1).toNat = (x (-6) 14).toNat := congrArg Bool.toNat (h114 (-6))
      have b7469 := hb (x (-6) 1)
      have b7470 := hb (x (-6) 14)
      clear * - r7468 b7469 b7470 d7463
      omega
    have d7471 : (x (-7) 1).toNat = 0 := by
      have r7472 : (x (-6) 14).toNat + (x (-7) 1).toNat = 1 := by have q := hd14 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7473 := hb (x (-7) 1)
      have b7474 := hb (x (-6) 14)
      clear * - r7472 b7473 b7474 d7467
      omega
    have d7475 : (x (-7) 1 && x (-7) 14).toNat = 0 := by
      have r7476 := hand1 (x (-7) 1) (x (-7) 14)
      have b7477 := hb (x (-7) 1)
      have b7478 := hb (x (-7) 1 && x (-7) 14)
      clear * - r7476 b7477 b7478 d7471
      omega
    have d7479 : (x (-7) 1 && x (-7) 11).toNat = 0 := by
      have r7480 := hand1 (x (-7) 1) (x (-7) 11)
      have b7481 := hb (x (-7) 1)
      have b7482 := hb (x (-7) 1 && x (-7) 11)
      clear * - r7480 b7481 b7482 d7471
      omega
    have d7483 : (x (-7) 14).toNat = 0 := by
      have r7484 : (x (-7) 1).toNat = (x (-7) 14).toNat := congrArg Bool.toNat (h114 (-7))
      have b7485 := hb (x (-7) 1)
      have b7486 := hb (x (-7) 14)
      clear * - r7484 b7485 b7486 d7471
      omega
    have d7487 : (x (-7) 6).toNat = 0 := by
      have r7488 : (x (-7) 6).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp6 (-7))
      have b7489 := hb (x (-7) 6)
      have b7490 := hb (x (-7) 14)
      clear * - r7488 b7489 b7490 d7483
      omega
    have d7491 : (x (-7) 2).toNat = 0 := by
      have r7492 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
      have b7493 := hb (x (-7) 2)
      have b7494 := hb (x (-7) 14)
      clear * - r7492 b7493 b7494 d7483
      omega
    have d7495 : (x (-7) 3).toNat = 0 := by
      have r7496 : (x (-7) 2).toNat = (x (-7) 3).toNat := congrArg Bool.toNat (h23 (-7))
      have b7497 := hb (x (-7) 2)
      have b7498 := hb (x (-7) 3)
      clear * - r7496 b7497 b7498 d7491
      omega
    have d7499 : (x (-7) 11).toNat = 0 := by
      have r7500 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
      have b7501 := hb (x (-7) 3)
      have b7502 := hb (x (-7) 11)
      clear * - r7500 b7501 b7502 d7495
      omega
    have d7503 : (x (-7) 10).toNat = 0 := by
      have r7504 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
      have b7505 := hb (x (-7) 2)
      have b7506 := hb (x (-7) 10)
      clear * - r7504 b7505 b7506 d7491
      omega
    have d7507 : (x (-7) 13).toNat = 0 := by
      have r7508 : (x (-7) 13).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp13 (-7))
      have b7509 := hb (x (-7) 1)
      have b7510 := hb (x (-7) 13)
      clear * - r7508 b7509 b7510 d7471
      omega
    have d7511 : (x (-7) 5).toNat = 0 := by
      have r7512 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
      have b7513 := hb (x (-7) 5)
      have b7514 := hb (x (-7) 13)
      clear * - r7512 b7513 b7514 d7507
      omega
    have d7515 : (x (-7) 9).toNat = 0 := by
      have r7516 : (x (-7) 9).toNat ≤ (x (-7) 1).toNat := himp _ _ (hp9 (-7))
      have b7517 := hb (x (-7) 1)
      have b7518 := hb (x (-7) 9)
      clear * - r7516 b7517 b7518 d7471
      omega
    have d7519 : (x (-8) 1).toNat = 1 := by
      have r7520 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := by have q := hd14 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7521 := hb (x (-8) 1)
      have b7522 := hb (x (-7) 14)
      clear * - r7520 b7521 b7522 d7483
      omega
    have d7523 : (x (-8) 14).toNat = 1 := by
      have r7524 : (x (-8) 1).toNat = (x (-8) 14).toNat := congrArg Bool.toNat (h114 (-8))
      have b7525 := hb (x (-8) 1)
      have b7526 := hb (x (-8) 14)
      clear * - r7524 b7525 b7526 d7519
      omega
    have d7527 : (x (-9) 1).toNat = 0 := by
      have r7528 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7529 := hb (x (-9) 1)
      have b7530 := hb (x (-8) 14)
      clear * - r7528 b7529 b7530 d7523
      omega
    have d7531 : (x (-9) 1 && x (-9) 12).toNat = 0 := by
      have r7532 := hand1 (x (-9) 1) (x (-9) 12)
      have b7533 := hb (x (-9) 1)
      have b7534 := hb (x (-9) 1 && x (-9) 12)
      clear * - r7532 b7533 b7534 d7527
      omega
    have d7535 : (x (-9) 14).toNat = 0 := by
      have r7536 : (x (-9) 1).toNat = (x (-9) 14).toNat := congrArg Bool.toNat (h114 (-9))
      have b7537 := hb (x (-9) 1)
      have b7538 := hb (x (-9) 14)
      clear * - r7536 b7537 b7538 d7527
      omega
    have d7539 : (x (-9) 2).toNat = 0 := by
      have r7540 : (x (-9) 2).toNat ≤ (x (-9) 14).toNat := himp _ _ (hp2 (-9))
      have b7541 := hb (x (-9) 2)
      have b7542 := hb (x (-9) 14)
      clear * - r7540 b7541 b7542 d7535
      omega
    have d7543 : (x (-9) 3).toNat = 0 := by
      have r7544 : (x (-9) 2).toNat = (x (-9) 3).toNat := congrArg Bool.toNat (h23 (-9))
      have b7545 := hb (x (-9) 2)
      have b7546 := hb (x (-9) 3)
      clear * - r7544 b7545 b7546 d7539
      omega
    have d7547 : (x (-9) 3 && x (-9) 13).toNat = 0 := by
      have r7548 := hand1 (x (-9) 3) (x (-9) 13)
      have b7549 := hb (x (-9) 3)
      have b7550 := hb (x (-9) 3 && x (-9) 13)
      clear * - r7548 b7549 b7550 d7543
      omega
    have d7551 : (x (-9) 11).toNat = 0 := by
      have r7552 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
      have b7553 := hb (x (-9) 3)
      have b7554 := hb (x (-9) 11)
      clear * - r7552 b7553 b7554 d7543
      omega
    have d7555 : (x (-9) 13).toNat = 0 := by
      have r7556 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
      have b7557 := hb (x (-9) 1)
      have b7558 := hb (x (-9) 13)
      clear * - r7556 b7557 b7558 d7527
      omega
    have d7559 : (x (-9) 9 && x (-9) 13).toNat = 0 := by
      have r7560 := hand2 (x (-9) 9) (x (-9) 13)
      have b7561 := hb (x (-9) 13)
      have b7562 := hb (x (-9) 9 && x (-9) 13)
      clear * - r7560 b7561 b7562 d7555
      omega
    have d7563 : (x (-9) 9).toNat = 0 := by
      have r7564 : (x (-9) 9).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp9 (-9))
      have b7565 := hb (x (-9) 1)
      have b7566 := hb (x (-9) 9)
      clear * - r7564 b7565 b7566 d7527
      omega
    have d7567 : (x (-10) 1).toNat = 1 := by
      have r7568 : (x (-9) 14).toNat + (x (-10) 1).toNat = 1 := by have q := hd14 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7569 := hb (x (-10) 1)
      have b7570 := hb (x (-9) 14)
      clear * - r7568 b7569 b7570 d7535
      omega
    have d7571 : (x (-10) 14).toNat = 1 := by
      have r7572 : (x (-10) 1).toNat = (x (-10) 14).toNat := congrArg Bool.toNat (h114 (-10))
      have b7573 := hb (x (-10) 1)
      have b7574 := hb (x (-10) 14)
      clear * - r7572 b7573 b7574 d7567
      omega
    have d7575 : (x (-2) 2 && x (-2) 11).toNat = 1 := by
      have r7576 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b7577 := hb (x (-6) 6)
      have b7578 := hb (x 0 9)
      have b7579 := hb (x (-1) 1 && x (-1) 10)
      have b7580 := hb (x (-2) 2 && x (-2) 11)
      have b7581 := hb (x (-3) 3 && x (-3) 12)
      have b7582 := hb (x (-4) 4 && x (-4) 13)
      have b7583 := hb (x (-5) 5 && x (-5) 14)
      clear * - r7576 b7577 b7578 b7579 b7580 b7581 b7582 b7583 g1 d7295 d7375 d6341 d6373 d6389
      omega
    have d7584 : (x (-2) 11).toNat = 1 := by
      have r7585 := hand2 (x (-2) 2) (x (-2) 11)
      have b7586 := hb (x (-2) 11)
      have b7587 := hb (x (-2) 2 && x (-2) 11)
      clear * - r7585 b7586 b7587 d7575
      omega
    have d7588 : (x (-2) 3).toNat = 1 := by
      have r7589 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
      have b7590 := hb (x (-2) 3)
      have b7591 := hb (x (-2) 11)
      clear * - r7589 b7590 b7591 d7584
      omega
    have d7592 : (x (-2) 2).toNat = 1 := by
      have r7593 : (x (-2) 2).toNat = (x (-2) 3).toNat := congrArg Bool.toNat (h23 (-2))
      have b7594 := hb (x (-2) 2)
      have b7595 := hb (x (-2) 3)
      clear * - r7593 b7594 b7595 d7588
      omega
    have d7596 : (x 0 12).toNat = 0 := by
      have r7597 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7598 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e7599 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b7600 := hb (x (-3) 3)
      have b7601 := hb (x (-2) 2)
      have b7602 := hb (x (-1) 13)
      have b7603 := hb (x 0 12)
      clear * - r7597 e7598 e7599 b7600 b7601 b7602 b7603 d7327 d7592 d7371
      omega
    have d7604 : (x 0 4).toNat = 0 := by
      have r7605 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
      have b7606 := hb (x 0 4)
      have b7607 := hb (x 0 12)
      clear * - r7605 b7606 b7607 d7596
      omega
    have d7608 : (x 0 4 && x 0 14).toNat = 0 := by
      have r7609 := hand1 (x 0 4) (x 0 14)
      have b7610 := hb (x 0 4)
      have b7611 := hb (x 0 4 && x 0 14)
      clear * - r7609 b7610 b7611 d7604
      omega
    have d7612 : (x 1 12).toNat = 0 := by
      have r7613 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7614 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e7615 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b7616 := hb (x (-2) 3)
      have b7617 := hb (x (-1) 2)
      have b7618 := hb (x 0 13)
      have b7619 := hb (x 1 12)
      clear * - r7613 e7614 e7615 b7616 b7617 b7618 b7619 d7311 d7588
      omega
    have d7620 : (x 0 13).toNat = 0 := by
      have r7621 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7622 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e7623 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b7624 := hb (x (-2) 3)
      have b7625 := hb (x (-1) 2)
      have b7626 := hb (x 0 13)
      have b7627 := hb (x 1 12)
      clear * - r7621 e7622 e7623 b7624 b7625 b7626 b7627 d7612 d7311 d7588
      omega
    have d7628 : (x 0 2 && x 0 13).toNat = 0 := by
      have r7629 := hand2 (x 0 2) (x 0 13)
      have b7630 := hb (x 0 13)
      have b7631 := hb (x 0 2 && x 0 13)
      clear * - r7629 b7630 b7631 d7620
      omega
    have d7632 : (x 1 8).toNat = 0 := by
      have r7633 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7634 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
      have e7635 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
      have e7636 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
      have e7637 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
      have e7638 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
      have e7639 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
      have b7640 := hb (x (-6) 7)
      have b7641 := hb (x (-5) 6)
      have b7642 := hb (x (-4) 5)
      have b7643 := hb (x (-3) 4)
      have b7644 := hb (x (-2) 11)
      have b7645 := hb (x (-1) 10)
      have b7646 := hb (x 0 9)
      have b7647 := hb (x 1 8)
      clear * - r7633 e7634 e7635 e7636 e7637 e7638 e7639 b7640 b7641 b7642 b7643 b7644 b7645 b7646 b7647 g1 d7319 d7584 d7423
      omega
    cases h7648 : x 0 2
    · have f7649 : (x 0 2).toNat = 0 := by rw [h7648]; rfl
      have d7650 : (x 0 2 && x 0 8).toNat = 0 := by
        have r7651 := hand1 (x 0 2) (x 0 8)
        have b7652 := hb (x 0 2)
        have b7653 := hb (x 0 2 && x 0 8)
        clear * - r7651 b7652 b7653 f7649
        omega
      have d7654 : (x 0 3).toNat = 0 := by
        have r7655 : (x 0 2).toNat = (x 0 3).toNat := congrArg Bool.toNat (h23 0)
        have b7656 := hb (x 0 2)
        have b7657 := hb (x 0 3)
        clear * - r7655 b7656 b7657 f7649
        omega
      have d7658 : (x 0 3 && x 0 8).toNat = 0 := by
        have r7659 := hand1 (x 0 3) (x 0 8)
        have b7660 := hb (x 0 3)
        have b7661 := hb (x 0 3 && x 0 8)
        clear * - r7659 b7660 b7661 d7654
        omega
      have d7662 : (x 0 11).toNat = 0 := by
        have r7663 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
        have b7664 := hb (x 0 3)
        have b7665 := hb (x 0 11)
        clear * - r7663 b7664 b7665 d7654
        omega
      have d7666 : (x 0 7 && x 0 11).toNat = 0 := by
        have r7667 := hand2 (x 0 7) (x 0 11)
        have b7668 := hb (x 0 11)
        have b7669 := hb (x 0 7 && x 0 11)
        clear * - r7667 b7668 b7669 d7662
        omega
      have d7670 : (x 2 13).toNat = 1 := by
        have r7671 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b7672 := hb (x 0 2)
        have b7673 := hb (x 2 13)
        have b7674 := hb (x 1 1 && x 1 14)
        clear * - r7671 b7672 b7673 b7674 d7051 f7649
        omega
      have d7675 : (x 3 12).toNat = 0 := by
        have r7676 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7677 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e7678 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b7679 := hb (x 0 3)
        have b7680 := hb (x 1 2)
        have b7681 := hb (x 2 13)
        have b7682 := hb (x 3 12)
        clear * - r7676 e7677 e7678 b7679 b7680 b7681 b7682 d7670 d7267 d7654
        omega
      have d7683 : (x 3 4).toNat = 0 := by
        have r7684 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
        have b7685 := hb (x 3 4)
        have b7686 := hb (x 3 12)
        clear * - r7684 b7685 b7686 d7675
        omega
      have d7687 : (x 3 4 && x 3 8).toNat = 0 := by
        have r7688 := hand1 (x 3 4) (x 3 8)
        have b7689 := hb (x 3 4)
        have b7690 := hb (x 3 4 && x 3 8)
        clear * - r7688 b7689 b7690 d7683
        omega
      have d7691 : (x (-2) 2 && x (-2) 13).toNat = 1 := by
        have r7692 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b7693 := hb (x (-4) 4)
        have b7694 := hb (x 0 11)
        have b7695 := hb (x (-1) 1 && x (-1) 12)
        have b7696 := hb (x (-2) 2 && x (-2) 13)
        have b7697 := hb (x (-3) 3 && x (-3) 14)
        clear * - r7692 b7693 b7694 b7695 b7696 b7697 d7662 d7291 d7351 d6325
        omega
      have d7698 : (x (-2) 13).toNat = 1 := by
        have r7699 := hand2 (x (-2) 2) (x (-2) 13)
        have b7700 := hb (x (-2) 13)
        have b7701 := hb (x (-2) 2 && x (-2) 13)
        clear * - r7699 b7700 b7701 d7691
        omega
      have d7702 : (x (-1) 12).toNat = 0 := by
        have r7703 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7704 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e7705 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b7706 := hb (x (-4) 3)
        have b7707 := hb (x (-3) 2)
        have b7708 := hb (x (-2) 13)
        have b7709 := hb (x (-1) 12)
        clear * - r7703 e7704 e7705 b7706 b7707 b7708 b7709 d7698 d7367
        omega
      have d7710 : (x (-1) 8 && x (-1) 12).toNat = 0 := by
        have r7711 := hand2 (x (-1) 8) (x (-1) 12)
        have b7712 := hb (x (-1) 12)
        have b7713 := hb (x (-1) 8 && x (-1) 12)
        clear * - r7711 b7712 b7713 d7702
        omega
      have d7714 : (x (-1) 4).toNat = 0 := by
        have r7715 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
        have b7716 := hb (x (-1) 4)
        have b7717 := hb (x (-1) 12)
        clear * - r7715 b7716 b7717 d7702
        omega
      have d7718 : (x (-4) 3).toNat = 0 := by
        have r7719 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7720 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e7721 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b7722 := hb (x (-4) 3)
        have b7723 := hb (x (-3) 2)
        have b7724 := hb (x (-2) 13)
        have b7725 := hb (x (-1) 12)
        clear * - r7719 e7720 e7721 b7722 b7723 b7724 b7725 d7702 d7698 d7367
        omega
      have d7726 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
        have r7727 := hand1 (x (-4) 3) (x (-4) 12)
        have b7728 := hb (x (-4) 3)
        have b7729 := hb (x (-4) 3 && x (-4) 12)
        clear * - r7727 b7728 b7729 d7718
        omega
      have d7730 : (x (-4) 2).toNat = 0 := by
        have r7731 : (x (-4) 2).toNat = (x (-4) 3).toNat := congrArg Bool.toNat (h23 (-4))
        have b7732 := hb (x (-4) 2)
        have b7733 := hb (x (-4) 3)
        clear * - r7731 b7732 b7733 d7718
        omega
      have d7734 : (x (-4) 2 && x (-4) 12).toNat = 0 := by
        have r7735 := hand1 (x (-4) 2) (x (-4) 12)
        have b7736 := hb (x (-4) 2)
        have b7737 := hb (x (-4) 2 && x (-4) 12)
        clear * - r7735 b7736 b7737 d7730
        omega
      have d7738 : (x (-4) 11).toNat = 0 := by
        have r7739 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
        have b7740 := hb (x (-4) 3)
        have b7741 := hb (x (-4) 11)
        clear * - r7739 b7740 b7741 d7718
        omega
      have d7742 : (x (-6) 4 && x (-6) 14).toNat = 1 := by
        have r7743 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b7744 := hb (x (-7) 5)
        have b7745 := hb (x (-2) 10)
        have b7746 := hb (x (-3) 1 && x (-3) 11)
        have b7747 := hb (x (-4) 2 && x (-4) 12)
        have b7748 := hb (x (-5) 3 && x (-5) 13)
        have b7749 := hb (x (-6) 4 && x (-6) 14)
        clear * - r7743 b7744 b7745 b7746 b7747 b7748 b7749 d6265 d6309 d7734 d7435 d7511
        omega
      have d7750 : (x (-6) 4).toNat = 1 := by
        have r7751 := hand1 (x (-6) 4) (x (-6) 14)
        have b7752 := hb (x (-6) 4)
        have b7753 := hb (x (-6) 4 && x (-6) 14)
        clear * - r7751 b7752 b7753 d7742
        omega
      have d7754 : (x (-6) 12).toNat = 1 := by
        have r7755 : (x (-6) 4).toNat ≤ (x (-6) 12).toNat := himp _ _ (hp4 (-6))
        have b7756 := hb (x (-6) 4)
        have b7757 := hb (x (-6) 12)
        clear * - r7755 b7756 b7757 d7750
        omega
      have d7758 : (x (-8) 2).toNat = 0 := by
        have r7759 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7760 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e7761 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b7762 := hb (x (-9) 3)
        have b7763 := hb (x (-8) 2)
        have b7764 := hb (x (-7) 13)
        have b7765 := hb (x (-6) 12)
        clear * - r7759 e7760 e7761 b7762 b7763 b7764 b7765 d7754 d7507 d7543
        omega
      have d7766 : (x (-8) 2 && x (-8) 12).toNat = 0 := by
        have r7767 := hand1 (x (-8) 2) (x (-8) 12)
        have b7768 := hb (x (-8) 2)
        have b7769 := hb (x (-8) 2 && x (-8) 12)
        clear * - r7767 b7768 b7769 d7758
        omega
      have d7770 : (x (-8) 3).toNat = 0 := by
        have r7771 : (x (-8) 2).toNat = (x (-8) 3).toNat := congrArg Bool.toNat (h23 (-8))
        have b7772 := hb (x (-8) 2)
        have b7773 := hb (x (-8) 3)
        clear * - r7771 b7772 b7773 d7758
        omega
      have d7774 : (x (-8) 11).toNat = 0 := by
        have r7775 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
        have b7776 := hb (x (-8) 3)
        have b7777 := hb (x (-8) 11)
        clear * - r7775 b7776 b7777 d7770
        omega
      have d7778 : (x (-8) 10).toNat = 0 := by
        have r7779 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
        have b7780 := hb (x (-8) 2)
        have b7781 := hb (x (-8) 10)
        clear * - r7779 b7780 b7781 d7758
        omega
      have d7782 : (x (-6) 13).toNat = 1 := by
        have r7783 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b7784 := hb (x (-8) 2)
        have b7785 := hb (x (-6) 13)
        have b7786 := hb (x (-7) 1 && x (-7) 14)
        clear * - r7783 b7784 b7785 b7786 d7475 d7758
        omega
      have d7787 : (x (-5) 12).toNat = 0 := by
        have r7788 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7789 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e7790 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b7791 := hb (x (-8) 3)
        have b7792 := hb (x (-7) 2)
        have b7793 := hb (x (-6) 13)
        have b7794 := hb (x (-5) 12)
        clear * - r7788 e7789 e7790 b7791 b7792 b7793 b7794 d7782 d7491 d7770
        omega
      have d7795 : (x (-5) 4).toNat = 0 := by
        have r7796 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
        have b7797 := hb (x (-5) 4)
        have b7798 := hb (x (-5) 12)
        clear * - r7796 b7797 b7798 d7787
        omega
      have d7799 : (x (-6) 5 && x (-6) 14).toNat = 1 := by
        have r7800 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b7801 := hb (x (-7) 6)
        have b7802 := hb (x (-1) 9)
        have b7803 := hb (x (-2) 1 && x (-2) 10)
        have b7804 := hb (x (-3) 2 && x (-3) 11)
        have b7805 := hb (x (-4) 3 && x (-4) 12)
        have b7806 := hb (x (-5) 4 && x (-5) 13)
        have b7807 := hb (x (-6) 5 && x (-6) 14)
        clear * - r7800 b7801 b7802 b7803 b7804 b7805 b7806 b7807 d6241 d6281 d6313 d7726 d7447 d7487
        omega
      have d7808 : (x (-6) 5).toNat = 1 := by
        have r7809 := hand1 (x (-6) 5) (x (-6) 14)
        have b7810 := hb (x (-6) 5)
        have b7811 := hb (x (-6) 5 && x (-6) 14)
        clear * - r7809 b7810 b7811 d7799
        omega
      have d7812 : (x (-1) 8).toNat = 0 := by
        have r7813 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7814 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e7815 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e7816 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e7817 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e7818 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e7819 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b7820 := hb (x (-8) 7)
        have b7821 := hb (x (-7) 6)
        have b7822 := hb (x (-6) 5)
        have b7823 := hb (x (-5) 4)
        have b7824 := hb (x (-4) 11)
        have b7825 := hb (x (-3) 10)
        have b7826 := hb (x (-2) 9)
        have b7827 := hb (x (-1) 8)
        clear * - r7813 e7814 e7815 e7816 e7817 e7818 e7819 b7820 b7821 b7822 b7823 b7824 b7825 b7826 b7827 d7387 d7738 d7795 d7808 d7487
        omega
      have d7828 : (x (-2) 9).toNat = 0 := by
        have r7829 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e7830 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
        have e7831 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
        have e7832 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
        have e7833 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
        have e7834 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
        have e7835 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
        have b7836 := hb (x (-8) 7)
        have b7837 := hb (x (-7) 6)
        have b7838 := hb (x (-6) 5)
        have b7839 := hb (x (-5) 4)
        have b7840 := hb (x (-4) 11)
        have b7841 := hb (x (-3) 10)
        have b7842 := hb (x (-2) 9)
        have b7843 := hb (x (-1) 8)
        clear * - r7829 e7830 e7831 e7832 e7833 e7834 e7835 b7836 b7837 b7838 b7839 b7840 b7841 b7842 b7843 d7812 d7387 d7738 d7795 d7808 d7487
        omega
      have d7844 : (x (-2) 2 && x (-2) 9).toNat = 0 := by
        have r7845 := hand2 (x (-2) 2) (x (-2) 9)
        have b7846 := hb (x (-2) 9)
        have b7847 := hb (x (-2) 2 && x (-2) 9)
        clear * - r7845 b7846 b7847 d7828
        omega
      have d7848 : (x (-2) 9 && x (-2) 13).toNat = 0 := by
        have r7849 := hand1 (x (-2) 9) (x (-2) 13)
        have b7850 := hb (x (-2) 9)
        have b7851 := hb (x (-2) 9 && x (-2) 13)
        clear * - r7849 b7850 b7851 d7828
        omega
      have r7852 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7853 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7854 : (x 7 1).toNat + (x 6 2).toNat + (x 5 3).toNat + (x 4 4).toNat + (x 3 5).toNat + (x 2 6).toNat + (x 1 7).toNat + (x 0 8).toNat + (x (-1) 9).toNat + (x (-2) 10).toNat + (x (-3) 11).toNat + (x (-4) 12).toNat + (x (-5) 13).toNat + (x (-6) 14).toNat = 3 := by have q := hcount 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7855 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7856 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7857 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e7858 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e7859 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e7860 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e7861 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e7862 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have r7863 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7864 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
      have e7865 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
      have e7866 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
      have e7867 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
      have e7868 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
      have e7869 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
      have r7870 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7871 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e7872 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e7873 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e7874 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e7875 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e7876 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have r7877 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7878 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e7879 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e7880 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e7881 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e7882 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e7883 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have r7884 : 1 ≤ (x 0 4).toNat + (x (-1) 1 && x (-1) 5).toNat + (x (-2) 2 && x (-2) 6).toNat + (x (-3) 3 && x (-3) 7).toNat + (x (-4) 4 && x (-4) 8).toNat + (x (-5) 5 && x (-5) 9).toNat + (x (-6) 6 && x (-6) 10).toNat + (x (-7) 7 && x (-7) 11).toNat + (x (-8) 8 && x (-8) 12).toNat + (x (-9) 9 && x (-9) 13).toNat + (x (-10) 10 && x (-10) 14).toNat + (x (-11) 11).toNat := by have q := hcov4 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7885 : (x (-1) 1 && x (-1) 5).toNat = (x (-1) 5).toNat := handr _ _ (fun h => hp13 (-1) (hp5 (-1) (h)))
      have e7886 : (x (-10) 10 && x (-10) 14).toNat = (x (-10) 10).toNat := handl _ _ (fun h => hp2 (-10) (hp10 (-10) (h)))
      have r7887 : 1 ≤ (x 7 4).toNat + (x 6 1 && x 6 5).toNat + (x 5 2 && x 5 6).toNat + (x 4 3 && x 4 7).toNat + (x 3 4 && x 3 8).toNat + (x 2 5 && x 2 9).toNat + (x 1 6 && x 1 10).toNat + (x 0 7 && x 0 11).toNat + (x (-1) 8 && x (-1) 12).toNat + (x (-2) 9 && x (-2) 13).toNat + (x (-3) 10 && x (-3) 14).toNat + (x (-4) 11).toNat := by have q := hcov4 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e7888 : (x 6 1 && x 6 5).toNat = (x 6 5).toNat := handr _ _ (fun h => hp13 6 (hp5 6 (h)))
      have e7889 : (x (-3) 10 && x (-3) 14).toNat = (x (-3) 10).toNat := handl _ _ (fun h => hp2 (-3) (hp10 (-3) (h)))
      have r7890 : 1 ≤ (x 3 5).toNat + (x 2 1 && x 2 6).toNat + (x 1 2 && x 1 7).toNat + (x 0 3 && x 0 8).toNat + (x (-1) 4 && x (-1) 9).toNat + (x (-2) 5 && x (-2) 10).toNat + (x (-3) 6 && x (-3) 11).toNat + (x (-4) 7 && x (-4) 12).toNat + (x (-5) 8 && x (-5) 13).toNat + (x (-6) 9 && x (-6) 14).toNat + (x (-7) 10).toNat := by have q := hcov5 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7891 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7892 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7893 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7894 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7895 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7896 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r7897 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
      have r7898 := hand2 (x (-2) 2) (x (-2) 6)
      have r7899 := hand2 (x (-8) 8) (x (-8) 12)
      have r7900 := hand2 (x 4 3) (x 4 7)
      have r7901 := hand1 (x 2 5) (x 2 9)
      have r7902 := hand2 (x 2 5) (x 2 9)
      have r7903 := hand2 (x 2 1) (x 2 6)
      have r7904 := hand2 (x (-4) 7) (x (-4) 12)
      have r7905 := hand1 (x (-6) 9) (x (-6) 14)
      have r7906 := hand2 (x (-4) 6) (x (-4) 12)
      have r7907 := hand1 (x (-6) 8) (x (-6) 14)
      have r7908 := hand1 (x (-10) 4) (x (-10) 14)
      have r7909 := hand2 (x (-10) 2) (x (-10) 13)
      have r7910 := hand2 (x (-11) 3) (x (-11) 14)
      have r7911 := hand1 (x 2 2) (x 2 13)
      have r7912 := hand1 (x 6 2) (x 6 13)
      have b7913 := hb (x (-15) 7)
      have b7914 := hb (x (-14) 6)
      have b7915 := hb (x (-13) 5)
      have b7916 := hb (x (-13) 7)
      have b7917 := hb (x (-12) 4)
      have b7918 := hb (x (-12) 6)
      have b7919 := hb (x (-11) 5)
      have b7920 := hb (x (-11) 11)
      have b7921 := hb (x (-11) 14)
      have b7922 := hb (x (-10) 4)
      have b7923 := hb (x (-10) 10)
      have b7924 := hb (x (-10) 13)
      have b7925 := hb (x (-10) 14)
      have b7926 := hb (x (-9) 9)
      have b7927 := hb (x (-9) 11)
      have b7928 := hb (x (-9) 12)
      have b7929 := hb (x (-9) 13)
      have b7930 := hb (x (-8) 8)
      have b7931 := hb (x (-8) 10)
      have b7932 := hb (x (-8) 11)
      have b7933 := hb (x (-8) 12)
      have b7934 := hb (x (-7) 9)
      have b7935 := hb (x (-7) 10)
      have b7936 := hb (x (-7) 11)
      have b7937 := hb (x (-6) 8)
      have b7938 := hb (x (-6) 9)
      have b7939 := hb (x (-6) 10)
      have b7940 := hb (x (-6) 14)
      have b7941 := hb (x (-5) 8)
      have b7942 := hb (x (-5) 9)
      have b7943 := hb (x (-5) 13)
      have b7944 := hb (x (-4) 7)
      have b7945 := hb (x (-4) 8)
      have b7946 := hb (x (-4) 11)
      have b7947 := hb (x (-4) 12)
      have b7948 := hb (x (-3) 6)
      have b7949 := hb (x (-3) 7)
      have b7950 := hb (x (-3) 10)
      have b7951 := hb (x (-3) 11)
      have b7952 := hb (x (-3) 14)
      have b7953 := hb (x (-2) 5)
      have b7954 := hb (x (-2) 6)
      have b7955 := hb (x (-2) 10)
      have b7956 := hb (x (-2) 13)
      have b7957 := hb (x (-1) 4)
      have b7958 := hb (x (-1) 5)
      have b7959 := hb (x (-1) 9)
      have b7960 := hb (x (-1) 12)
      have b7961 := hb (x 0 3)
      have b7962 := hb (x 0 4)
      have b7963 := hb (x 0 7)
      have b7964 := hb (x 0 8)
      have b7965 := hb (x 0 11)
      have b7966 := hb (x 1 2)
      have b7967 := hb (x 1 3)
      have b7968 := hb (x 1 6)
      have b7969 := hb (x 1 7)
      have b7970 := hb (x 1 10)
      have b7971 := hb (x 2 1)
      have b7972 := hb (x 2 2)
      have b7973 := hb (x 2 5)
      have b7974 := hb (x 2 6)
      have b7975 := hb (x 2 9)
      have b7976 := hb (x 3 1)
      have b7977 := hb (x 3 4)
      have b7978 := hb (x 3 5)
      have b7979 := hb (x 3 8)
      have b7980 := hb (x 4 4)
      have b7981 := hb (x 4 7)
      have b7982 := hb (x 4 11)
      have b7983 := hb (x 5 3)
      have b7984 := hb (x 5 6)
      have b7985 := hb (x 5 10)
      have b7986 := hb (x 6 2)
      have b7987 := hb (x 6 5)
      have b7988 := hb (x 6 9)
      have b7989 := hb (x 7 1)
      have b7990 := hb (x 7 4)
      have b7991 := hb (x 7 8)
      have b7992 := hb (x 8 3)
      have b7993 := hb (x 8 11)
      have b7994 := hb (x 9 2)
      have b7995 := hb (x 10 1)
      have b7996 := hb (x (-2) 2 && x (-2) 6)
      have b7997 := hb (x (-3) 3 && x (-3) 7)
      have b7998 := hb (x (-4) 4 && x (-4) 8)
      have b7999 := hb (x (-5) 5 && x (-5) 9)
      have b8000 := hb (x (-6) 6 && x (-6) 10)
      have b8001 := hb (x (-7) 7 && x (-7) 11)
      have b8002 := hb (x (-8) 8 && x (-8) 12)
      have b8003 := hb (x (-9) 9 && x (-9) 13)
      have b8004 := hb (x 5 2 && x 5 6)
      have b8005 := hb (x 4 3 && x 4 7)
      have b8006 := hb (x 3 4 && x 3 8)
      have b8007 := hb (x 2 5 && x 2 9)
      have b8008 := hb (x 1 6 && x 1 10)
      have b8009 := hb (x 0 7 && x 0 11)
      have b8010 := hb (x (-1) 8 && x (-1) 12)
      have b8011 := hb (x (-2) 9 && x (-2) 13)
      have b8012 := hb (x 2 1 && x 2 6)
      have b8013 := hb (x 1 2 && x 1 7)
      have b8014 := hb (x 0 3 && x 0 8)
      have b8015 := hb (x (-1) 4 && x (-1) 9)
      have b8016 := hb (x (-2) 5 && x (-2) 10)
      have b8017 := hb (x (-3) 6 && x (-3) 11)
      have b8018 := hb (x (-4) 7 && x (-4) 12)
      have b8019 := hb (x (-5) 8 && x (-5) 13)
      have b8020 := hb (x (-6) 9 && x (-6) 14)
      have b8021 := hb (x 1 1 && x 1 7)
      have b8022 := hb (x 0 2 && x 0 8)
      have b8023 := hb (x (-1) 3 && x (-1) 9)
      have b8024 := hb (x (-2) 4 && x (-2) 10)
      have b8025 := hb (x (-3) 5 && x (-3) 11)
      have b8026 := hb (x (-4) 6 && x (-4) 12)
      have b8027 := hb (x (-5) 7 && x (-5) 13)
      have b8028 := hb (x (-6) 8 && x (-6) 14)
      have b8029 := hb (x (-1) 1 && x (-1) 8)
      have b8030 := hb (x (-2) 2 && x (-2) 9)
      have b8031 := hb (x (-3) 3 && x (-3) 10)
      have b8032 := hb (x (-4) 4 && x (-4) 11)
      have b8033 := hb (x (-5) 5 && x (-5) 12)
      have b8034 := hb (x (-6) 6 && x (-6) 13)
      have b8035 := hb (x (-7) 7 && x (-7) 14)
      have b8036 := hb (x (-7) 1 && x (-7) 11)
      have b8037 := hb (x (-8) 2 && x (-8) 12)
      have b8038 := hb (x (-9) 3 && x (-9) 13)
      have b8039 := hb (x (-10) 4 && x (-10) 14)
      have b8040 := hb (x (-9) 1 && x (-9) 12)
      have b8041 := hb (x (-10) 2 && x (-10) 13)
      have b8042 := hb (x (-11) 3 && x (-11) 14)
      have b8043 := hb (x 3 1 && x 3 12)
      have b8044 := hb (x 2 2 && x 2 13)
      have b8045 := hb (x 1 3 && x 1 14)
      have b8046 := hb (x 7 1 && x 7 12)
      have b8047 := hb (x 6 2 && x 6 13)
      have b8048 := hb (x 5 3 && x 5 14)
      linarith only [r7852, r7853, r7854, r7855, r7856, e7857, e7858, e7859, e7860, e7861, e7862, r7863, e7864, e7865, e7866, e7867, e7868, e7869, r7870, e7871, e7872, e7873, e7874, e7875, e7876, r7877, e7878, e7879, e7880, e7881, e7882, e7883, r7884, e7885, e7886, r7887, e7888, e7889, r7890, r7891, r7892, r7893, r7894, r7895, r7896, r7897, r7898, r7899, r7900, r7901, r7902, r7903, r7904, r7905, r7906, r7907, r7908, r7909, r7910, r7911, r7912, b7913, b7914, b7915, b7916, b7917, b7918, b7919, b7920, b7921, b7922, b7923, b7924, b7925, b7926, b7927, b7928, b7929, b7930, b7931, b7932, b7933, b7934, b7935, b7936, b7937, b7938, b7939, b7940, b7941, b7942, b7943, b7944, b7945, b7946, b7947, b7948, b7949, b7950, b7951, b7952, b7953, b7954, b7955, b7956, b7957, b7958, b7959, b7960, b7961, b7962, b7963, b7964, b7965, b7966, b7967, b7968, b7969, b7970, b7971, b7972, b7973, b7974, b7975, b7976, b7977, b7978, b7979, b7980, b7981, b7982, b7983, b7984, b7985, b7986, b7987, b7988, b7989, b7990, b7991, b7992, b7993, b7994, b7995, b7996, b7997, b7998, b7999, b8000, b8001, b8002, b8003, b8004, b8005, b8006, b8007, b8008, b8009, b8010, b8011, b8012, b8013, b8014, b8015, b8016, b8017, b8018, b8019, b8020, b8021, b8022, b8023, b8024, b8025, b8026, b8027, b8028, b8029, b8030, b8031, b8032, b8033, b8034, b8035, b8036, b8037, b8038, b8039, b8040, b8041, b8042, b8043, b8044, b8045, b8046, b8047, b8048, d7571, d7563, d7551, d7555, d7778, d7774, d7515, d7503, d7499, d7467, d7459, d7443, d7738, d7359, d7387, d6293, d7347, d6265, d7698, d7714, d7331, d6241, d7702, d7654, d7604, g0, d7662, d7267, d7279, d7259, d7283, d7091, d7103, d7683, d7119, d7231, d7219, d7235, d7171, d7203, d7199, d7383, d6353, d6385, d6413, d6441, d7559, d7223, d7687, d7263, d7666, d7710, d7848, d7275, d7658, d6261, d6289, d6321, d7455, d7067, d7650, d6257, d6285, d6317, d7451, d7299, d7844, d7379, d6345, d6377, d6405, d6433, d7479, d7766, d7547, d7531, d7107, d7055, d7175, d7135]
    · have f8049 : (x 0 2).toNat = 1 := by rw [h7648]; rfl
      have d8050 : (x 0 3).toNat = 1 := by
        have r8051 : (x 0 2).toNat = (x 0 3).toNat := congrArg Bool.toNat (h23 0)
        have b8052 := hb (x 0 2)
        have b8053 := hb (x 0 3)
        clear * - r8051 b8052 b8053 f8049
        omega
      have d8054 : (x 3 12).toNat = 0 := by
        have r8055 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8056 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e8057 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b8058 := hb (x 0 3)
        have b8059 := hb (x 1 2)
        have b8060 := hb (x 2 13)
        have b8061 := hb (x 3 12)
        clear * - r8055 e8056 e8057 b8058 b8059 b8060 b8061 d7267 d8050
        omega
      have d8062 : (x 3 4).toNat = 0 := by
        have r8063 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
        have b8064 := hb (x 3 4)
        have b8065 := hb (x 3 12)
        clear * - r8063 b8064 b8065 d8054
        omega
      have d8066 : (x 2 13).toNat = 0 := by
        have r8067 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8068 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e8069 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b8070 := hb (x 0 3)
        have b8071 := hb (x 1 2)
        have b8072 := hb (x 2 13)
        have b8073 := hb (x 3 12)
        clear * - r8067 e8068 e8069 b8070 b8071 b8072 b8073 d8054 d7267 d8050
        omega
      have d8074 : (x 2 2 && x 2 13).toNat = 0 := by
        have r8075 := hand2 (x 2 2) (x 2 13)
        have b8076 := hb (x 2 13)
        have b8077 := hb (x 2 2 && x 2 13)
        clear * - r8075 b8076 b8077 d8066
        omega
      have d8078 : (x 2 5).toNat = 0 := by
        have r8079 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
        have b8080 := hb (x 2 5)
        have b8081 := hb (x 2 13)
        clear * - r8079 b8080 b8081 d8066
        omega
      have d8082 : (x 2 12).toNat = 0 := by
        have r8083 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8084 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e8085 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b8086 := hb (x (-1) 3)
        have b8087 := hb (x 0 2)
        have b8088 := hb (x 1 13)
        have b8089 := hb (x 2 12)
        clear * - r8083 e8084 e8085 b8086 b8087 b8088 b8089 d7071 f8049 d7315
        omega
      have d8090 : (x 2 2 && x 2 12).toNat = 0 := by
        have r8091 := hand2 (x 2 2) (x 2 12)
        have b8092 := hb (x 2 12)
        have b8093 := hb (x 2 2 && x 2 12)
        clear * - r8091 b8092 b8093 d8082
        omega
      have d8094 : (x 2 4).toNat = 0 := by
        have r8095 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
        have b8096 := hb (x 2 4)
        have b8097 := hb (x 2 12)
        clear * - r8095 b8096 b8097 d8082
        omega
      have d8098 : (x 2 4 && x 2 9).toNat = 0 := by
        have r8099 := hand1 (x 2 4) (x 2 9)
        have b8100 := hb (x 2 4)
        have b8101 := hb (x 2 4 && x 2 9)
        clear * - r8099 b8100 b8101 d8094
        omega
      have d8102 : (x 4 11).toNat = 1 := by
        have r8103 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8104 := hb (x 0 4)
        have b8105 := hb (x 4 11)
        have b8106 := hb (x 3 1 && x 3 12)
        have b8107 := hb (x 2 2 && x 2 13)
        have b8108 := hb (x 1 3 && x 1 14)
        clear * - r8103 b8104 b8105 b8106 b8107 b8108 d7107 d8074 d7055 d7604
        omega
      have d8109 : (x 4 3).toNat = 1 := by
        have r8110 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
        have b8111 := hb (x 4 3)
        have b8112 := hb (x 4 11)
        clear * - r8110 b8111 b8112 d8102
        omega
      have d8113 : (x 7 12).toNat = 0 := by
        have r8114 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8115 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e8116 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b8117 := hb (x 4 3)
        have b8118 := hb (x 5 2)
        have b8119 := hb (x 6 13)
        have b8120 := hb (x 7 12)
        clear * - r8114 e8115 e8116 b8117 b8118 b8119 b8120 d7227 d8109
        omega
      have d8121 : (x 7 4).toNat = 0 := by
        have r8122 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
        have b8123 := hb (x 7 4)
        have b8124 := hb (x 7 12)
        clear * - r8122 b8123 b8124 d8113
        omega
      have d8125 : (x 6 13).toNat = 0 := by
        have r8126 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8127 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e8128 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b8129 := hb (x 4 3)
        have b8130 := hb (x 5 2)
        have b8131 := hb (x 6 13)
        have b8132 := hb (x 7 12)
        clear * - r8126 e8127 e8128 b8129 b8130 b8131 b8132 d8113 d7227 d8109
        omega
      have d8133 : (x 6 3 && x 6 13).toNat = 0 := by
        have r8134 := hand2 (x 6 3) (x 6 13)
        have b8135 := hb (x 6 13)
        have b8136 := hb (x 6 3 && x 6 13)
        clear * - r8134 b8135 b8136 d8125
        omega
      have d8137 : (x 6 5).toNat = 0 := by
        have r8138 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
        have b8139 := hb (x 6 5)
        have b8140 := hb (x 6 13)
        clear * - r8138 b8139 b8140 d8125
        omega
      have d8141 : (x 4 10).toNat = 1 := by
        have r8142 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b8143 := hb (x (-1) 5)
        have b8144 := hb (x 4 10)
        have b8145 := hb (x 3 1 && x 3 11)
        have b8146 := hb (x 2 2 && x 2 12)
        have b8147 := hb (x 1 3 && x 1 13)
        have b8148 := hb (x 0 4 && x 0 14)
        clear * - r8142 b8143 b8144 b8145 b8146 b8147 b8148 d7111 d8090 d7075 d7608 d7331
        omega
      have d8149 : (x 7 8).toNat = 0 := by
        have r8150 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8151 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e8152 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e8153 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e8154 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e8155 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e8156 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b8157 := hb (x 0 7)
        have b8158 := hb (x 1 6)
        have b8159 := hb (x 2 5)
        have b8160 := hb (x 3 4)
        have b8161 := hb (x 4 11)
        have b8162 := hb (x 5 10)
        have b8163 := hb (x 6 9)
        have b8164 := hb (x 7 8)
        clear * - r8150 e8151 e8152 e8153 e8154 e8155 e8156 b8157 b8158 b8159 b8160 b8161 b8162 b8163 b8164 d7235 d8102 d8062 d8078 d7259
        omega
      have d8165 : (x 6 9).toNat = 0 := by
        have r8166 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8167 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e8168 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e8169 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e8170 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e8171 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e8172 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b8173 := hb (x 0 7)
        have b8174 := hb (x 1 6)
        have b8175 := hb (x 2 5)
        have b8176 := hb (x 3 4)
        have b8177 := hb (x 4 11)
        have b8178 := hb (x 5 10)
        have b8179 := hb (x 6 9)
        have b8180 := hb (x 7 8)
        clear * - r8166 e8167 e8168 e8169 e8170 e8171 e8172 b8173 b8174 b8175 b8176 b8177 b8178 b8179 b8180 d8149 d7235 d8102 d8062 d8078 d7259
        omega
      have d8181 : (x 0 7).toNat = 0 := by
        have r8182 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8183 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e8184 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e8185 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e8186 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e8187 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e8188 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b8189 := hb (x 0 7)
        have b8190 := hb (x 1 6)
        have b8191 := hb (x 2 5)
        have b8192 := hb (x 3 4)
        have b8193 := hb (x 4 11)
        have b8194 := hb (x 5 10)
        have b8195 := hb (x 6 9)
        have b8196 := hb (x 7 8)
        clear * - r8182 e8183 e8184 e8185 e8186 e8187 e8188 b8189 b8190 b8191 b8192 b8193 b8194 b8195 b8196 d8149 d8165 d7235 d8102 d8062 d8078 d7259
        omega
      have d8197 : (x 6 8).toNat = 0 := by
        have r8198 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8199 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e8200 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e8201 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e8202 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e8203 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e8204 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b8205 := hb (x (-1) 7)
        have b8206 := hb (x 0 6)
        have b8207 := hb (x 1 5)
        have b8208 := hb (x 2 4)
        have b8209 := hb (x 3 11)
        have b8210 := hb (x 4 10)
        have b8211 := hb (x 5 9)
        have b8212 := hb (x 6 8)
        clear * - r8198 e8199 e8200 e8201 e8202 e8203 e8204 b8205 b8206 b8207 b8208 b8209 b8210 b8211 b8212 d7155 d8141 d7255 d8094 d7079
        omega
      have d8213 : (x 0 6).toNat = 0 := by
        have r8214 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8215 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e8216 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e8217 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e8218 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e8219 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e8220 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b8221 := hb (x (-1) 7)
        have b8222 := hb (x 0 6)
        have b8223 := hb (x 1 5)
        have b8224 := hb (x 2 4)
        have b8225 := hb (x 3 11)
        have b8226 := hb (x 4 10)
        have b8227 := hb (x 5 9)
        have b8228 := hb (x 6 8)
        clear * - r8214 e8215 e8216 e8217 e8218 e8219 e8220 b8221 b8222 b8223 b8224 b8225 b8226 b8227 b8228 d8197 d7155 d8141 d7255 d8094 d7079
        omega
      have d8229 : (x 0 6 && x 0 11).toNat = 0 := by
        have r8230 := hand1 (x 0 6) (x 0 11)
        have b8231 := hb (x 0 6)
        have b8232 := hb (x 0 6 && x 0 11)
        clear * - r8230 b8231 b8232 d8213
        omega
      have d8233 : (x (-1) 7).toNat = 0 := by
        have r8234 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e8235 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
        have e8236 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
        have e8237 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
        have e8238 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
        have e8239 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
        have e8240 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
        have b8241 := hb (x (-1) 7)
        have b8242 := hb (x 0 6)
        have b8243 := hb (x 1 5)
        have b8244 := hb (x 2 4)
        have b8245 := hb (x 3 11)
        have b8246 := hb (x 4 10)
        have b8247 := hb (x 5 9)
        have b8248 := hb (x 6 8)
        clear * - r8234 e8235 e8236 e8237 e8238 e8239 e8240 b8241 b8242 b8243 b8244 b8245 b8246 b8247 b8248 d8197 d7155 d8141 d7255 d8094 d7079 d8213
        omega
      have d8249 : (x (-1) 7 && x (-1) 12).toNat = 0 := by
        have r8250 := hand1 (x (-1) 7) (x (-1) 12)
        have b8251 := hb (x (-1) 7)
        have b8252 := hb (x (-1) 7 && x (-1) 12)
        clear * - r8250 b8251 b8252 d8233
        omega
      have r8253 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r8254 : (x 8 1).toNat + (x 7 2).toNat + (x 6 3).toNat + (x 5 4).toNat + (x 4 5).toNat + (x 3 6).toNat + (x 2 7).toNat + (x 1 8).toNat + (x 0 9).toNat + (x (-1) 10).toNat + (x (-2) 11).toNat + (x (-3) 12).toNat + (x (-4) 13).toNat + (x (-5) 14).toNat = 3 := by have q := hcount 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r8255 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8256 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
      have e8257 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
      have e8258 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
      have e8259 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
      have e8260 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
      have e8261 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
      have r8262 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8263 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
      have e8264 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
      have e8265 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
      have e8266 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
      have e8267 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
      have e8268 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
      have r8269 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8270 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e8271 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e8272 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e8273 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e8274 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e8275 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have r8276 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8277 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
      have e8278 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
      have e8279 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
      have e8280 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
      have e8281 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
      have e8282 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
      have r8283 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8284 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
      have e8285 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
      have r8286 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8287 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e8288 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have r8289 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e8290 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e8291 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have r8292 : 1 ≤ (x 6 5).toNat + (x 5 1 && x 5 6).toNat + (x 4 2 && x 4 7).toNat + (x 3 3 && x 3 8).toNat + (x 2 4 && x 2 9).toNat + (x 1 5 && x 1 10).toNat + (x 0 6 && x 0 11).toNat + (x (-1) 7 && x (-1) 12).toNat + (x (-2) 8 && x (-2) 13).toNat + (x (-3) 9 && x (-3) 14).toNat + (x (-4) 10).toNat := by have q := hcov5 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r8293 : 1 ≤ (x 3 6).toNat + (x 2 1 && x 2 7).toNat + (x 1 2 && x 1 8).toNat + (x 0 3 && x 0 9).toNat + (x (-1) 4 && x (-1) 10).toNat + (x (-2) 5 && x (-2) 11).toNat + (x (-3) 6 && x (-3) 12).toNat + (x (-4) 7 && x (-4) 13).toNat + (x (-5) 8 && x (-5) 14).toNat + (x (-6) 9).toNat := by have q := hcov6 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r8294 : 1 ≤ (x 0 7).toNat + (x (-1) 1 && x (-1) 8).toNat + (x (-2) 2 && x (-2) 9).toNat + (x (-3) 3 && x (-3) 10).toNat + (x (-4) 4 && x (-4) 11).toNat + (x (-5) 5 && x (-5) 12).toNat + (x (-6) 6 && x (-6) 13).toNat + (x (-7) 7 && x (-7) 14).toNat + (x (-8) 8).toNat := by have q := hcov7 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r8295 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r8296 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r8297 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r8298 : 1 ≤ (x (-8) 11).toNat + (x (-9) 1 && x (-9) 12).toNat + (x (-10) 2 && x (-10) 13).toNat + (x (-11) 3 && x (-11) 14).toNat + (x (-12) 4).toNat := by have q := hcov11 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r8299 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r8300 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r8301 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := by have q := hcov13 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r8302 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
      have r8303 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
      have r8304 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
      have r8305 := hand2 (x 4 2) (x 4 7)
      have r8306 := hand1 (x (-2) 8) (x (-2) 13)
      have r8307 := hand2 (x 2 1) (x 2 7)
      have r8308 := hand1 (x (-2) 5) (x (-2) 11)
      have r8309 := hand1 (x (-4) 7) (x (-4) 13)
      have r8310 := hand2 (x (-2) 2) (x (-2) 9)
      have r8311 := hand2 (x (-4) 3) (x (-4) 12)
      have r8312 := hand1 (x (-6) 5) (x (-6) 14)
      have r8313 := hand1 (x (-4) 2) (x (-4) 12)
      have r8314 := hand1 (x (-6) 4) (x (-6) 14)
      have r8315 := hand2 (x 8 1) (x 8 11)
      have r8316 := hand2 (x (-10) 2) (x (-10) 13)
      have r8317 := hand2 (x (-11) 3) (x (-11) 14)
      have r8318 := hand2 (x 4 2) (x 4 13)
      have b8319 := hb (x (-15) 7)
      have b8320 := hb (x (-14) 6)
      have b8321 := hb (x (-13) 5)
      have b8322 := hb (x (-12) 4)
      have b8323 := hb (x (-11) 11)
      have b8324 := hb (x (-11) 14)
      have b8325 := hb (x (-10) 10)
      have b8326 := hb (x (-10) 13)
      have b8327 := hb (x (-9) 7)
      have b8328 := hb (x (-9) 9)
      have b8329 := hb (x (-9) 12)
      have b8330 := hb (x (-8) 6)
      have b8331 := hb (x (-8) 7)
      have b8332 := hb (x (-8) 8)
      have b8333 := hb (x (-8) 11)
      have b8334 := hb (x (-7) 3)
      have b8335 := hb (x (-7) 5)
      have b8336 := hb (x (-7) 6)
      have b8337 := hb (x (-7) 10)
      have b8338 := hb (x (-6) 2)
      have b8339 := hb (x (-6) 4)
      have b8340 := hb (x (-6) 5)
      have b8341 := hb (x (-6) 9)
      have b8342 := hb (x (-5) 3)
      have b8343 := hb (x (-5) 4)
      have b8344 := hb (x (-5) 8)
      have b8345 := hb (x (-5) 11)
      have b8346 := hb (x (-5) 13)
      have b8347 := hb (x (-5) 14)
      have b8348 := hb (x (-4) 2)
      have b8349 := hb (x (-4) 7)
      have b8350 := hb (x (-4) 10)
      have b8351 := hb (x (-4) 11)
      have b8352 := hb (x (-4) 12)
      have b8353 := hb (x (-4) 13)
      have b8354 := hb (x (-3) 6)
      have b8355 := hb (x (-3) 9)
      have b8356 := hb (x (-3) 10)
      have b8357 := hb (x (-3) 12)
      have b8358 := hb (x (-3) 13)
      have b8359 := hb (x (-2) 4)
      have b8360 := hb (x (-2) 5)
      have b8361 := hb (x (-2) 8)
      have b8362 := hb (x (-2) 9)
      have b8363 := hb (x (-2) 10)
      have b8364 := hb (x (-2) 11)
      have b8365 := hb (x (-2) 12)
      have b8366 := hb (x (-1) 4)
      have b8367 := hb (x (-1) 8)
      have b8368 := hb (x (-1) 9)
      have b8369 := hb (x (-1) 10)
      have b8370 := hb (x 0 3)
      have b8371 := hb (x 0 7)
      have b8372 := hb (x 0 9)
      have b8373 := hb (x 1 2)
      have b8374 := hb (x 1 8)
      have b8375 := hb (x 2 1)
      have b8376 := hb (x 2 3)
      have b8377 := hb (x 2 4)
      have b8378 := hb (x 2 7)
      have b8379 := hb (x 2 11)
      have b8380 := hb (x 3 2)
      have b8381 := hb (x 3 6)
      have b8382 := hb (x 4 5)
      have b8383 := hb (x 4 7)
      have b8384 := hb (x 4 13)
      have b8385 := hb (x 5 4)
      have b8386 := hb (x 5 6)
      have b8387 := hb (x 5 12)
      have b8388 := hb (x 6 3)
      have b8389 := hb (x 6 5)
      have b8390 := hb (x 6 11)
      have b8391 := hb (x 7 2)
      have b8392 := hb (x 7 4)
      have b8393 := hb (x 8 1)
      have b8394 := hb (x 8 11)
      have b8395 := hb (x 9 10)
      have b8396 := hb (x 10 9)
      have b8397 := hb (x 11 8)
      have b8398 := hb (x 5 1 && x 5 6)
      have b8399 := hb (x 4 2 && x 4 7)
      have b8400 := hb (x 3 3 && x 3 8)
      have b8401 := hb (x 2 4 && x 2 9)
      have b8402 := hb (x 1 5 && x 1 10)
      have b8403 := hb (x 0 6 && x 0 11)
      have b8404 := hb (x (-1) 7 && x (-1) 12)
      have b8405 := hb (x (-2) 8 && x (-2) 13)
      have b8406 := hb (x (-3) 9 && x (-3) 14)
      have b8407 := hb (x 2 1 && x 2 7)
      have b8408 := hb (x 1 2 && x 1 8)
      have b8409 := hb (x 0 3 && x 0 9)
      have b8410 := hb (x (-1) 4 && x (-1) 10)
      have b8411 := hb (x (-2) 5 && x (-2) 11)
      have b8412 := hb (x (-3) 6 && x (-3) 12)
      have b8413 := hb (x (-4) 7 && x (-4) 13)
      have b8414 := hb (x (-5) 8 && x (-5) 14)
      have b8415 := hb (x (-1) 1 && x (-1) 8)
      have b8416 := hb (x (-2) 2 && x (-2) 9)
      have b8417 := hb (x (-3) 3 && x (-3) 10)
      have b8418 := hb (x (-4) 4 && x (-4) 11)
      have b8419 := hb (x (-5) 5 && x (-5) 12)
      have b8420 := hb (x (-6) 6 && x (-6) 13)
      have b8421 := hb (x (-7) 7 && x (-7) 14)
      have b8422 := hb (x (-2) 1 && x (-2) 10)
      have b8423 := hb (x (-3) 2 && x (-3) 11)
      have b8424 := hb (x (-4) 3 && x (-4) 12)
      have b8425 := hb (x (-5) 4 && x (-5) 13)
      have b8426 := hb (x (-6) 5 && x (-6) 14)
      have b8427 := hb (x (-3) 1 && x (-3) 11)
      have b8428 := hb (x (-4) 2 && x (-4) 12)
      have b8429 := hb (x (-5) 3 && x (-5) 13)
      have b8430 := hb (x (-6) 4 && x (-6) 14)
      have b8431 := hb (x 8 1 && x 8 11)
      have b8432 := hb (x 7 2 && x 7 12)
      have b8433 := hb (x 6 3 && x 6 13)
      have b8434 := hb (x 5 4 && x 5 14)
      have b8435 := hb (x (-9) 1 && x (-9) 12)
      have b8436 := hb (x (-10) 2 && x (-10) 13)
      have b8437 := hb (x (-11) 3 && x (-11) 14)
      have b8438 := hb (x 1 1 && x 1 12)
      have b8439 := hb (x 0 2 && x 0 13)
      have b8440 := hb (x (-1) 3 && x (-1) 14)
      have b8441 := hb (x 5 1 && x 5 12)
      have b8442 := hb (x 4 2 && x 4 13)
      have b8443 := hb (x 3 3 && x 3 14)
      have b8444 := hb (x (-5) 1 && x (-5) 14)
      linarith only [r8253, r8254, r8255, e8256, e8257, e8258, e8259, e8260, e8261, r8262, e8263, e8264, e8265, e8266, e8267, e8268, r8269, e8270, e8271, e8272, e8273, e8274, e8275, r8276, e8277, e8278, e8279, e8280, e8281, e8282, r8283, e8284, e8285, r8286, e8287, e8288, r8289, e8290, e8291, r8292, r8293, r8294, r8295, r8296, r8297, r8298, r8299, r8300, r8301, r8302, r8303, r8304, r8305, r8306, r8307, r8308, r8309, r8310, r8311, r8312, r8313, r8314, r8315, r8316, r8317, r8318, b8319, b8320, b8321, b8322, b8323, b8324, b8325, b8326, b8327, b8328, b8329, b8330, b8331, b8332, b8333, b8334, b8335, b8336, b8337, b8338, b8339, b8340, b8341, b8342, b8343, b8344, b8345, b8346, b8347, b8348, b8349, b8350, b8351, b8352, b8353, b8354, b8355, b8356, b8357, b8358, b8359, b8360, b8361, b8362, b8363, b8364, b8365, b8366, b8367, b8368, b8369, b8370, b8371, b8372, b8373, b8374, b8375, b8376, b8377, b8378, b8379, b8380, b8381, b8382, b8383, b8384, b8385, b8386, b8387, b8388, b8389, b8390, b8391, b8392, b8393, b8394, b8395, b8396, b8397, b8398, b8399, b8400, b8401, b8402, b8403, b8404, b8405, b8406, b8407, b8408, b8409, b8410, b8411, b8412, b8413, b8414, b8415, b8416, b8417, b8418, b8419, b8420, b8421, b8422, b8423, b8424, b8425, b8426, b8427, b8428, b8429, b8430, b8431, b8432, b8433, b8434, b8435, b8436, b8437, b8438, b8439, b8440, b8441, b8442, b8443, b8444, d7563, d7495, d7511, d7487, d7503, d7431, d7439, d7443, d7415, d7359, d7395, d7387, d7391, d6265, d7584, d6241, d7319, d8050, d8181, g1, d7267, d7632, d7091, d8094, d7243, d7239, d7219, d8137, d7211, d8121, d7183, d7207, d7151, d7251, d8098, d7083, d8229, d8249, d7355, d7271, d6237, d7323, d7363, d7419, d7299, d7379, d6345, d6377, d6405, d6433, d6281, d6313, d7447, d6309, d7435, d7215, d8133, d7139, d7531, d7063, d7628, d7307, d7147, d7099, d7411]

theorem cycle_power_fifteen_tight_type_sequence_shape_rules_core_v81_90 (x : ℤ → Fin 16 → Bool)
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
    (h114 : ∀ p, x p 1 = x p 14)
    (h23 : ∀ p, x p 2 = x p 3)
    (g0 : (x 0 8).toNat = 1) (g1 : (x 0 9).toNat = 0) : False := cycle_power_fifteen_tight_type_sequence_shape_rules_core_v81_90_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 h114 h23 g0 g1
