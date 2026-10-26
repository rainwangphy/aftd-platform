import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0101

Topic: combinatorics   Node: 76ea5602be9e

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 21 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0101_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-5) 5).toNat = 0)
    (g1 : (x (-2) 10).toNat = 0)
    (g2 : (x 0 1).toNat = 1)
    (g3 : (x 0 2).toNat = 0)
    (g4 : (x 0 5).toNat = 0)
    (g5 : (x 0 6).toNat = 0)
    (g6 : (x 0 7).toNat = 1)
    (g7 : (x 0 10).toNat = 0)
    (g8 : (x 1 6).toNat = 0)
    (g9 : (x 3 2).toNat = 0)
    (g10 : (x 3 4).toNat = 0)
    (g11 : (x 0 1 && x 0 6).toNat = 0)
    (g12 : (x 0 1 && x 0 10).toNat = 0)
    (g13 : (x 3 3 && x 3 12).toNat = 0)
    (g14 : (x 1 5 && x 1 14).toNat = 0)
    (g15 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g16 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g17 : (x 3 2 && x 3 12).toNat = 0)
    (g18 : (x 1 4 && x 1 14).toNat = 0)
    (g19 : (x 0 1 && x 0 14).toNat = 0)
    (g20 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d48241 : (x 7 8).toNat = 0 := by
    have r48242 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e48243 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e48244 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e48245 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e48246 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e48247 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e48248 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b48249 := hb (x 0 7)
    have b48250 := hb (x 1 6)
    have b48251 := hb (x 2 5)
    have b48252 := hb (x 3 4)
    have b48253 := hb (x 4 11)
    have b48254 := hb (x 5 10)
    have b48255 := hb (x 6 9)
    have b48256 := hb (x 7 8)
    clear * - r48242 e48243 e48244 e48245 e48246 e48247 e48248 b48249 b48250 b48251 b48252 b48253 b48254 b48255 b48256 g10 g8 g6
    omega
  have d48257 : (x 6 9).toNat = 0 := by
    have r48258 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e48259 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e48260 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e48261 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e48262 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e48263 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e48264 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b48265 := hb (x 0 7)
    have b48266 := hb (x 1 6)
    have b48267 := hb (x 2 5)
    have b48268 := hb (x 3 4)
    have b48269 := hb (x 4 11)
    have b48270 := hb (x 5 10)
    have b48271 := hb (x 6 9)
    have b48272 := hb (x 7 8)
    clear * - r48258 e48259 e48260 e48261 e48262 e48263 e48264 b48265 b48266 b48267 b48268 b48269 b48270 b48271 b48272 d48241 g10 g8 g6
    omega
  have d48273 : (x 5 10).toNat = 0 := by
    have r48274 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e48275 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e48276 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e48277 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e48278 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e48279 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e48280 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b48281 := hb (x 0 7)
    have b48282 := hb (x 1 6)
    have b48283 := hb (x 2 5)
    have b48284 := hb (x 3 4)
    have b48285 := hb (x 4 11)
    have b48286 := hb (x 5 10)
    have b48287 := hb (x 6 9)
    have b48288 := hb (x 7 8)
    clear * - r48274 e48275 e48276 e48277 e48278 e48279 e48280 b48281 b48282 b48283 b48284 b48285 b48286 b48287 b48288 d48241 d48257 g10 g8 g6
    omega
  have d48289 : (x 5 1 && x 5 10).toNat = 0 := by
    have r48290 := hand2 (x 5 1) (x 5 10)
    have b48291 := hb (x 5 10)
    have b48292 := hb (x 5 1 && x 5 10)
    clear * - r48290 b48291 b48292 d48273
    omega
  have d48293 : (x 4 11).toNat = 0 := by
    have r48294 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e48295 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e48296 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e48297 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e48298 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e48299 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e48300 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b48301 := hb (x 0 7)
    have b48302 := hb (x 1 6)
    have b48303 := hb (x 2 5)
    have b48304 := hb (x 3 4)
    have b48305 := hb (x 4 11)
    have b48306 := hb (x 5 10)
    have b48307 := hb (x 6 9)
    have b48308 := hb (x 7 8)
    clear * - r48294 e48295 e48296 e48297 e48298 e48299 e48300 b48301 b48302 b48303 b48304 b48305 b48306 b48307 b48308 d48241 d48257 d48273 g10 g8 g6
    omega
  have d48309 : (x 4 1 && x 4 11).toNat = 0 := by
    have r48310 := hand2 (x 4 1) (x 4 11)
    have b48311 := hb (x 4 11)
    have b48312 := hb (x 4 1 && x 4 11)
    clear * - r48310 b48311 b48312 d48293
    omega
  have d48313 : (x 2 3 && x 2 13).toNat = 1 := by
    have r48314 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := hcov10 5
    have b48315 := hb (x 0 5)
    have b48316 := hb (x 5 10)
    have b48317 := hb (x 4 1 && x 4 11)
    have b48318 := hb (x 3 2 && x 3 12)
    have b48319 := hb (x 2 3 && x 2 13)
    have b48320 := hb (x 1 4 && x 1 14)
    clear * - r48314 b48315 b48316 b48317 b48318 b48319 b48320 d48273 d48309 g17 g18 g4
    omega
  have d48321 : (x 2 3).toNat = 1 := by
    have r48322 := hand1 (x 2 3) (x 2 13)
    have b48323 := hb (x 2 3)
    have b48324 := hb (x 2 3 && x 2 13)
    clear * - r48322 b48323 b48324 d48313
    omega
  have d48325 : (x 5 12).toNat = 0 := by
    have r48326 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
    have e48327 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e48328 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b48329 := hb (x 2 3)
    have b48330 := hb (x 3 2)
    have b48331 := hb (x 4 13)
    have b48332 := hb (x 5 12)
    clear * - r48326 e48327 e48328 b48329 b48330 b48331 b48332 g9 d48321
    omega
  have d48333 : (x 4 13).toNat = 0 := by
    have r48334 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
    have e48335 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e48336 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b48337 := hb (x 2 3)
    have b48338 := hb (x 3 2)
    have b48339 := hb (x 4 13)
    have b48340 := hb (x 5 12)
    clear * - r48334 e48335 e48336 b48337 b48338 b48339 b48340 d48325 g9 d48321
    omega
  have d48341 : (x 2 2).toNat = 1 := by
    have r48342 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
    have b48343 := hb (x 2 2)
    have b48344 := hb (x 4 13)
    have b48345 := hb (x 3 1 && x 3 14)
    clear * - r48342 b48343 b48344 b48345 d48333 g20
    omega
  have d48346 : (x 2 14).toNat = 1 := by
    have r48347 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
    have b48348 := hb (x 2 2)
    have b48349 := hb (x 2 14)
    clear * - r48347 b48348 b48349 d48341
    omega
  have d48350 : (x 1 1).toNat = 0 := by
    have r48351 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
    have b48352 := hb (x 1 1)
    have b48353 := hb (x 2 14)
    clear * - r48351 b48352 b48353 d48346
    omega
  have d48354 : (x 1 13).toNat = 0 := by
    have r48355 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b48356 := hb (x 1 1)
    have b48357 := hb (x 1 13)
    clear * - r48355 b48356 b48357 d48350
    omega
  have d48358 : (x 1 5).toNat = 0 := by
    have r48359 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b48360 := hb (x 1 5)
    have b48361 := hb (x 1 13)
    clear * - r48359 b48360 b48361 d48354
    omega
  have d48362 : (x (-1) 2).toNat = 1 := by
    have r48363 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
    have b48364 := hb (x (-1) 2)
    have b48365 := hb (x 1 13)
    have b48366 := hb (x 0 1 && x 0 14)
    clear * - r48363 b48364 b48365 b48366 d48354 g19
    omega
  have d48367 : (x 1 12).toNat = 0 := by
    have r48368 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
    have e48369 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e48370 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b48371 := hb (x (-2) 3)
    have b48372 := hb (x (-1) 2)
    have b48373 := hb (x 0 13)
    have b48374 := hb (x 1 12)
    clear * - r48368 e48369 e48370 b48371 b48372 b48373 b48374 d48362
    omega
  have d48375 : (x 0 13).toNat = 0 := by
    have r48376 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
    have e48377 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e48378 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b48379 := hb (x (-2) 3)
    have b48380 := hb (x (-1) 2)
    have b48381 := hb (x 0 13)
    have b48382 := hb (x 1 12)
    clear * - r48376 e48377 e48378 b48379 b48380 b48381 b48382 d48367 d48362
    omega
  have d48383 : (x (-2) 3).toNat = 0 := by
    have r48384 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
    have e48385 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e48386 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b48387 := hb (x (-2) 3)
    have b48388 := hb (x (-1) 2)
    have b48389 := hb (x 0 13)
    have b48390 := hb (x 1 12)
    clear * - r48384 e48385 e48386 b48387 b48388 b48389 b48390 d48367 d48375 d48362
    omega
  have d48391 : (x (-2) 3 && x (-2) 12).toNat = 0 := by
    have r48392 := hand1 (x (-2) 3) (x (-2) 12)
    have b48393 := hb (x (-2) 3)
    have b48394 := hb (x (-2) 3 && x (-2) 12)
    clear * - r48392 b48393 b48394 d48383
    omega
  have d48395 : (x (-2) 3 && x (-2) 8).toNat = 0 := by
    have r48396 := hand1 (x (-2) 3) (x (-2) 8)
    have b48397 := hb (x (-2) 3)
    have b48398 := hb (x (-2) 3 && x (-2) 8)
    clear * - r48396 b48397 b48398 d48383
    omega
  have d48399 : (x 1 9).toNat = 0 := by
    have r48400 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
    have b48401 := hb (x 1 1)
    have b48402 := hb (x 1 9)
    clear * - r48400 b48401 b48402 d48350
    omega
  have d48403 : (x 4 2 && x 4 11).toNat = 0 := by
    have r48404 := hand2 (x 4 2) (x 4 11)
    have b48405 := hb (x 4 11)
    have b48406 := hb (x 4 2 && x 4 11)
    clear * - r48404 b48405 b48406 d48293
    omega
  have d48407 : (x 2 4 && x 2 13).toNat = 1 := by
    have r48408 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := hcov9 6
    have b48409 := hb (x 0 6)
    have b48410 := hb (x 6 9)
    have b48411 := hb (x 5 1 && x 5 10)
    have b48412 := hb (x 4 2 && x 4 11)
    have b48413 := hb (x 3 3 && x 3 12)
    have b48414 := hb (x 2 4 && x 2 13)
    have b48415 := hb (x 1 5 && x 1 14)
    clear * - r48408 b48409 b48410 b48411 b48412 b48413 b48414 b48415 d48257 d48289 d48403 g13 g14 g5
    omega
  have d48416 : (x 2 4).toNat = 1 := by
    have r48417 := hand1 (x 2 4) (x 2 13)
    have b48418 := hb (x 2 4)
    have b48419 := hb (x 2 4 && x 2 13)
    clear * - r48417 b48418 b48419 d48407
    omega
  have d48420 : (x 2 12).toNat = 1 := by
    have r48421 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b48422 := hb (x 2 4)
    have b48423 := hb (x 2 12)
    clear * - r48421 b48422 b48423 d48416
    omega
  have d48424 : (x (-1) 3).toNat = 0 := by
    have r48425 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
    have e48426 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e48427 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b48428 := hb (x (-1) 3)
    have b48429 := hb (x 0 2)
    have b48430 := hb (x 1 13)
    have b48431 := hb (x 2 12)
    clear * - r48425 e48426 e48427 b48428 b48429 b48430 b48431 d48420 d48354 g3
    omega
  have d48432 : (x (-1) 11).toNat = 0 := by
    have r48433 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b48434 := hb (x (-1) 3)
    have b48435 := hb (x (-1) 11)
    clear * - r48433 b48434 b48435 d48424
    omega
  have d48436 : (x (-1) 1 && x (-1) 11).toNat = 0 := by
    have r48437 := hand2 (x (-1) 1) (x (-1) 11)
    have b48438 := hb (x (-1) 11)
    have b48439 := hb (x (-1) 1 && x (-1) 11)
    clear * - r48437 b48438 b48439 d48432
    omega
  have d48440 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
    have r48441 := hand2 (x (-1) 2) (x (-1) 11)
    have b48442 := hb (x (-1) 11)
    have b48443 := hb (x (-1) 2 && x (-1) 11)
    clear * - r48441 b48442 b48443 d48432
    omega
  have d48444 : (x 6 8).toNat = 0 := by
    have r48445 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
    have e48446 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e48447 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e48448 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e48449 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e48450 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e48451 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b48452 := hb (x (-1) 7)
    have b48453 := hb (x 0 6)
    have b48454 := hb (x 1 5)
    have b48455 := hb (x 2 4)
    have b48456 := hb (x 3 11)
    have b48457 := hb (x 4 10)
    have b48458 := hb (x 5 9)
    have b48459 := hb (x 6 8)
    clear * - r48445 e48446 e48447 e48448 e48449 e48450 e48451 b48452 b48453 b48454 b48455 b48456 b48457 b48458 b48459 d48416 d48358 g5
    omega
  have d48460 : (x 5 9).toNat = 0 := by
    have r48461 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
    have e48462 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e48463 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e48464 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e48465 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e48466 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e48467 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b48468 := hb (x (-1) 7)
    have b48469 := hb (x 0 6)
    have b48470 := hb (x 1 5)
    have b48471 := hb (x 2 4)
    have b48472 := hb (x 3 11)
    have b48473 := hb (x 4 10)
    have b48474 := hb (x 5 9)
    have b48475 := hb (x 6 8)
    clear * - r48461 e48462 e48463 e48464 e48465 e48466 e48467 b48468 b48469 b48470 b48471 b48472 b48473 b48474 b48475 d48444 d48416 d48358 g5
    omega
  have d48476 : (x 4 10).toNat = 0 := by
    have r48477 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
    have e48478 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e48479 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e48480 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e48481 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e48482 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e48483 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b48484 := hb (x (-1) 7)
    have b48485 := hb (x 0 6)
    have b48486 := hb (x 1 5)
    have b48487 := hb (x 2 4)
    have b48488 := hb (x 3 11)
    have b48489 := hb (x 4 10)
    have b48490 := hb (x 5 9)
    have b48491 := hb (x 6 8)
    clear * - r48477 e48478 e48479 e48480 e48481 e48482 e48483 b48484 b48485 b48486 b48487 b48488 b48489 b48490 b48491 d48444 d48460 d48416 d48358 g5
    omega
  have d48492 : (x 3 11).toNat = 0 := by
    have r48493 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
    have e48494 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e48495 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e48496 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e48497 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e48498 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e48499 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b48500 := hb (x (-1) 7)
    have b48501 := hb (x 0 6)
    have b48502 := hb (x 1 5)
    have b48503 := hb (x 2 4)
    have b48504 := hb (x 3 11)
    have b48505 := hb (x 4 10)
    have b48506 := hb (x 5 9)
    have b48507 := hb (x 6 8)
    clear * - r48493 e48494 e48495 e48496 e48497 e48498 e48499 b48500 b48501 b48502 b48503 b48504 b48505 b48506 b48507 d48444 d48460 d48476 d48416 d48358 g5
    omega
  have d48508 : (x (-1) 7).toNat = 0 := by
    have r48509 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
    have e48510 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e48511 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e48512 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e48513 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e48514 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e48515 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b48516 := hb (x (-1) 7)
    have b48517 := hb (x 0 6)
    have b48518 := hb (x 1 5)
    have b48519 := hb (x 2 4)
    have b48520 := hb (x 3 11)
    have b48521 := hb (x 4 10)
    have b48522 := hb (x 5 9)
    have b48523 := hb (x 6 8)
    clear * - r48509 e48510 e48511 e48512 e48513 e48514 e48515 b48516 b48517 b48518 b48519 b48520 b48521 b48522 b48523 d48444 d48460 d48476 d48492 d48416 d48358 g5
    omega
  have d48524 : (x (-1) 2 && x (-1) 7).toNat = 0 := by
    have r48525 := hand2 (x (-1) 2) (x (-1) 7)
    have b48526 := hb (x (-1) 7)
    have b48527 := hb (x (-1) 2 && x (-1) 7)
    clear * - r48525 b48526 b48527 d48508
    omega
  have r48528 : (x 0 1).toNat + (x (-1) 2).toNat + (x (-2) 3).toNat + (x (-3) 4).toNat + (x (-4) 5).toNat + (x (-5) 6).toNat + (x (-6) 7).toNat + (x (-7) 8).toNat + (x (-8) 9).toNat + (x (-9) 10).toNat + (x (-10) 11).toNat + (x (-11) 12).toNat + (x (-12) 13).toNat + (x (-13) 14).toNat = 3 := hcount 1
  have r48529 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := hd8 (-2)
  have e48530 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
  have e48531 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
  have e48532 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
  have e48533 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
  have e48534 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
  have e48535 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
  have r48536 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := hd12 (-2)
  have e48537 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
  have e48538 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
  have r48539 : 1 ≤ (x 1 5).toNat + (x 0 1 && x 0 6).toNat + (x (-1) 2 && x (-1) 7).toNat + (x (-2) 3 && x (-2) 8).toNat + (x (-3) 4 && x (-3) 9).toNat + (x (-4) 5 && x (-4) 10).toNat + (x (-5) 6 && x (-5) 11).toNat + (x (-6) 7 && x (-6) 12).toNat + (x (-7) 8 && x (-7) 13).toNat + (x (-8) 9 && x (-8) 14).toNat + (x (-9) 10).toNat := hcov5 1
  have r48540 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := hcov9 1
  have r48541 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := hcov10 (-2)
  have r48542 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := hcov10 0
  have r48543 := hand2 (x (-3) 4) (x (-3) 9)
  have r48544 := hand2 (x (-4) 5) (x (-4) 10)
  have r48545 := hand2 (x (-5) 6) (x (-5) 11)
  have r48546 := hand1 (x (-6) 7) (x (-6) 12)
  have r48547 := hand1 (x (-7) 8) (x (-7) 13)
  have r48548 := hand1 (x (-8) 9) (x (-8) 14)
  have r48549 := hand1 (x (-3) 4) (x (-3) 13)
  have r48550 := hand1 (x (-4) 5) (x (-4) 14)
  have r48551 := hand1 (x (-4) 2) (x (-4) 12)
  have r48552 := hand1 (x (-5) 3) (x (-5) 13)
  have r48553 := hand1 (x (-6) 4) (x (-6) 14)
  have r48554 := hand2 (x (-2) 2) (x (-2) 12)
  have r48555 := hand2 (x (-3) 3) (x (-3) 13)
  have b48556 := hb (x (-13) 14)
  have b48557 := hb (x (-12) 13)
  have b48558 := hb (x (-11) 12)
  have b48559 := hb (x (-10) 11)
  have b48560 := hb (x (-9) 7)
  have b48561 := hb (x (-9) 10)
  have b48562 := hb (x (-8) 6)
  have b48563 := hb (x (-8) 9)
  have b48564 := hb (x (-7) 5)
  have b48565 := hb (x (-7) 8)
  have b48566 := hb (x (-6) 4)
  have b48567 := hb (x (-6) 7)
  have b48568 := hb (x (-5) 3)
  have b48569 := hb (x (-5) 5)
  have b48570 := hb (x (-5) 6)
  have b48571 := hb (x (-5) 11)
  have b48572 := hb (x (-4) 2)
  have b48573 := hb (x (-4) 5)
  have b48574 := hb (x (-4) 10)
  have b48575 := hb (x (-3) 4)
  have b48576 := hb (x (-3) 9)
  have b48577 := hb (x (-3) 13)
  have b48578 := hb (x (-2) 3)
  have b48579 := hb (x (-2) 8)
  have b48580 := hb (x (-2) 10)
  have b48581 := hb (x (-2) 12)
  have b48582 := hb (x (-1) 2)
  have b48583 := hb (x 0 1)
  have b48584 := hb (x 0 10)
  have b48585 := hb (x 1 5)
  have b48586 := hb (x 1 9)
  have b48587 := hb (x 0 1 && x 0 6)
  have b48588 := hb (x (-1) 2 && x (-1) 7)
  have b48589 := hb (x (-2) 3 && x (-2) 8)
  have b48590 := hb (x (-3) 4 && x (-3) 9)
  have b48591 := hb (x (-4) 5 && x (-4) 10)
  have b48592 := hb (x (-5) 6 && x (-5) 11)
  have b48593 := hb (x (-6) 7 && x (-6) 12)
  have b48594 := hb (x (-7) 8 && x (-7) 13)
  have b48595 := hb (x (-8) 9 && x (-8) 14)
  have b48596 := hb (x 0 1 && x 0 10)
  have b48597 := hb (x (-1) 2 && x (-1) 11)
  have b48598 := hb (x (-2) 3 && x (-2) 12)
  have b48599 := hb (x (-3) 4 && x (-3) 13)
  have b48600 := hb (x (-4) 5 && x (-4) 14)
  have b48601 := hb (x (-3) 1 && x (-3) 11)
  have b48602 := hb (x (-4) 2 && x (-4) 12)
  have b48603 := hb (x (-5) 3 && x (-5) 13)
  have b48604 := hb (x (-6) 4 && x (-6) 14)
  have b48605 := hb (x (-1) 1 && x (-1) 11)
  have b48606 := hb (x (-2) 2 && x (-2) 12)
  have b48607 := hb (x (-3) 3 && x (-3) 13)
  have b48608 := hb (x (-4) 4 && x (-4) 14)
  linarith only [r48528, r48529, e48530, e48531, e48532, e48533, e48534, e48535, r48536, e48537, e48538, r48539, r48540, r48541, r48542, r48543, r48544, r48545, r48546, r48547, r48548, r48549, r48550, r48551, r48552, r48553, r48554, r48555, b48556, b48557, b48558, b48559, b48560, b48561, b48562, b48563, b48564, b48565, b48566, b48567, b48568, b48569, b48570, b48571, b48572, b48573, b48574, b48575, b48576, b48577, b48578, b48579, b48580, b48581, b48582, b48583, b48584, b48585, b48586, b48587, b48588, b48589, b48590, b48591, b48592, b48593, b48594, b48595, b48596, b48597, b48598, b48599, b48600, b48601, b48602, b48603, b48604, b48605, b48606, b48607, b48608, g0, d48383, g1, d48362, g2, g7, d48358, d48399, g11, d48524, d48395, g12, d48440, d48391, g15, d48436, g16]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0101 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-5) 5).toNat = 0)
    (g1 : (x (-2) 10).toNat = 0)
    (g2 : (x 0 1).toNat = 1)
    (g3 : (x 0 2).toNat = 0)
    (g4 : (x 0 5).toNat = 0)
    (g5 : (x 0 6).toNat = 0)
    (g6 : (x 0 7).toNat = 1)
    (g7 : (x 0 10).toNat = 0)
    (g8 : (x 1 6).toNat = 0)
    (g9 : (x 3 2).toNat = 0)
    (g10 : (x 3 4).toNat = 0)
    (g11 : (x 0 1 && x 0 6).toNat = 0)
    (g12 : (x 0 1 && x 0 10).toNat = 0)
    (g13 : (x 3 3 && x 3 12).toNat = 0)
    (g14 : (x 1 5 && x 1 14).toNat = 0)
    (g15 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g16 : (x (-4) 4 && x (-4) 14).toNat = 0)
    (g17 : (x 3 2 && x 3 12).toNat = 0)
    (g18 : (x 1 4 && x 1 14).toNat = 0)
    (g19 : (x 0 1 && x 0 14).toNat = 0)
    (g20 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0101_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20
