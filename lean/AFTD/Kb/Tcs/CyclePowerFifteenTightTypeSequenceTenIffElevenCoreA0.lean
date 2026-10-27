import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_a0

Topic: combinatorics   Node: 53f1ee591b81

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core: under the layer-free tight-cover constraints for k = 15 and 47 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b1111.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b1111 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-2) 10).toNat = 0)
    (g2 : (x (-1) 9).toNat = 0)
    (g3 : (x 0 7).toNat = 1)
    (g4 : (x 0 10).toNat = 0)
    (g5 : (x 0 11).toNat = 1)
    (g6 : (x 1 2).toNat = 0)
    (g7 : (x 1 5).toNat = 0)
    (g8 : (x 1 6).toNat = 0)
    (g9 : (x 1 10).toNat = 0)
    (g10 : (x 1 14).toNat = 0)
    (g11 : (x 2 5).toNat = 0)
    (g12 : (x 2 9).toNat = 0)
    (g13 : (x 3 4).toNat = 0)
    (g14 : (x 3 8).toNat = 0)
    (g15 : (x 3 9).toNat = 0)
    (g16 : (x 3 12 && x 3 13).toNat = 0)
    (g17 : (x 2 13 && x 2 14).toNat = 0)
    (g18 : (x 3 4 && x 3 7).toNat = 0)
    (g19 : (x 2 5 && x 2 8).toNat = 0)
    (g20 : (x 1 6 && x 1 9).toNat = 0)
    (g21 : (x 0 7 && x 0 10).toNat = 0)
    (g22 : (x (-1) 8 && x (-1) 11).toNat = 0)
    (g23 : (x 3 7 && x 3 12).toNat = 0)
    (g24 : (x 2 8 && x 2 13).toNat = 0)
    (g25 : (x 1 9 && x 1 14).toNat = 0)
    (g26 : (x 6 2 && x 6 8).toNat = 0)
    (g27 : (x 5 3 && x 5 9).toNat = 0)
    (g28 : (x 4 4 && x 4 10).toNat = 0)
    (g29 : (x 3 5 && x 3 11).toNat = 0)
    (g30 : (x 2 6 && x 2 12).toNat = 0)
    (g31 : (x 1 7 && x 1 13).toNat = 0)
    (g32 : (x 4 8 && x 4 14).toNat = 0)
    (g33 : (x 3 5 && x 3 12).toNat = 0)
    (g34 : (x 2 6 && x 2 13).toNat = 0)
    (g35 : (x 1 7 && x 1 14).toNat = 0)
    (g36 : (x 3 4 && x 3 13).toNat = 0)
    (g37 : (x 2 5 && x 2 14).toNat = 0)
    (g38 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g39 : (x (-2) 2 && x (-2) 12).toNat = 0)
    (g40 : (x (-3) 3 && x (-3) 13).toNat = 0)
    (g41 : (x 2 4 && x 2 14).toNat = 0)
    (g42 : (x 3 4 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d25243 : (x 7 8).toNat = 0 := by
    have r25244 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25245 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e25246 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e25247 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e25248 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e25249 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e25250 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b25251 := hb (x 0 7)
    have b25252 := hb (x 1 6)
    have b25253 := hb (x 2 5)
    have b25254 := hb (x 3 4)
    have b25255 := hb (x 4 11)
    have b25256 := hb (x 5 10)
    have b25257 := hb (x 6 9)
    have b25258 := hb (x 7 8)
    clear * - r25244 e25245 e25246 e25247 e25248 e25249 e25250 b25251 b25252 b25253 b25254 b25255 b25256 b25257 b25258 g13 g11 g8 g3
    omega
  have d25259 : (x 7 1 && x 7 8).toNat = 0 := by
    have r25260 := hand2 (x 7 1) (x 7 8)
    have b25261 := hb (x 7 8)
    have b25262 := hb (x 7 1 && x 7 8)
    clear * - r25260 b25261 b25262 d25243
    omega
  have d25263 : (x 7 3 && x 7 8).toNat = 0 := by
    have r25264 := hand2 (x 7 3) (x 7 8)
    have b25265 := hb (x 7 8)
    have b25266 := hb (x 7 3 && x 7 8)
    clear * - r25264 b25265 b25266 d25243
    omega
  have d25267 : (x 7 8 && x 7 9).toNat = 0 := by
    have r25268 := hand1 (x 7 8) (x 7 9)
    have b25269 := hb (x 7 8)
    have b25270 := hb (x 7 8 && x 7 9)
    clear * - r25268 b25269 b25270 d25243
    omega
  have d25271 : (x 6 9).toNat = 0 := by
    have r25272 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25273 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e25274 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e25275 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e25276 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e25277 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e25278 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b25279 := hb (x 0 7)
    have b25280 := hb (x 1 6)
    have b25281 := hb (x 2 5)
    have b25282 := hb (x 3 4)
    have b25283 := hb (x 4 11)
    have b25284 := hb (x 5 10)
    have b25285 := hb (x 6 9)
    have b25286 := hb (x 7 8)
    clear * - r25272 e25273 e25274 e25275 e25276 e25277 e25278 b25279 b25280 b25281 b25282 b25283 b25284 b25285 b25286 d25243 g13 g11 g8 g3
    omega
  have d25287 : (x 6 2 && x 6 9).toNat = 0 := by
    have r25288 := hand2 (x 6 2) (x 6 9)
    have b25289 := hb (x 6 9)
    have b25290 := hb (x 6 2 && x 6 9)
    clear * - r25288 b25289 b25290 d25271
    omega
  have d25291 : (x 6 4 && x 6 9).toNat = 0 := by
    have r25292 := hand2 (x 6 4) (x 6 9)
    have b25293 := hb (x 6 9)
    have b25294 := hb (x 6 4 && x 6 9)
    clear * - r25292 b25293 b25294 d25271
    omega
  have d25295 : (x 6 9 && x 6 10).toNat = 0 := by
    have r25296 := hand1 (x 6 9) (x 6 10)
    have b25297 := hb (x 6 9)
    have b25298 := hb (x 6 9 && x 6 10)
    clear * - r25296 b25297 b25298 d25271
    omega
  have d25299 : (x 5 10).toNat = 0 := by
    have r25300 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25301 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e25302 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e25303 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e25304 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e25305 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e25306 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b25307 := hb (x 0 7)
    have b25308 := hb (x 1 6)
    have b25309 := hb (x 2 5)
    have b25310 := hb (x 3 4)
    have b25311 := hb (x 4 11)
    have b25312 := hb (x 5 10)
    have b25313 := hb (x 6 9)
    have b25314 := hb (x 7 8)
    clear * - r25300 e25301 e25302 e25303 e25304 e25305 e25306 b25307 b25308 b25309 b25310 b25311 b25312 b25313 b25314 d25243 d25271 g13 g11 g8 g3
    omega
  have d25315 : (x 5 3 && x 5 10).toNat = 0 := by
    have r25316 := hand2 (x 5 3) (x 5 10)
    have b25317 := hb (x 5 10)
    have b25318 := hb (x 5 3 && x 5 10)
    clear * - r25316 b25317 b25318 d25299
    omega
  have d25319 : (x 5 5 && x 5 10).toNat = 0 := by
    have r25320 := hand2 (x 5 5) (x 5 10)
    have b25321 := hb (x 5 10)
    have b25322 := hb (x 5 5 && x 5 10)
    clear * - r25320 b25321 b25322 d25299
    omega
  have d25323 : (x 5 10 && x 5 11).toNat = 0 := by
    have r25324 := hand1 (x 5 10) (x 5 11)
    have b25325 := hb (x 5 10)
    have b25326 := hb (x 5 10 && x 5 11)
    clear * - r25324 b25325 b25326 d25299
    omega
  have d25327 : (x 4 11).toNat = 0 := by
    have r25328 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e25329 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e25330 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e25331 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e25332 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e25333 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e25334 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b25335 := hb (x 0 7)
    have b25336 := hb (x 1 6)
    have b25337 := hb (x 2 5)
    have b25338 := hb (x 3 4)
    have b25339 := hb (x 4 11)
    have b25340 := hb (x 5 10)
    have b25341 := hb (x 6 9)
    have b25342 := hb (x 7 8)
    clear * - r25328 e25329 e25330 e25331 e25332 e25333 e25334 b25335 b25336 b25337 b25338 b25339 b25340 b25341 b25342 d25243 d25271 d25299 g13 g11 g8 g3
    omega
  have d25343 : (x 4 4 && x 4 11).toNat = 0 := by
    have r25344 := hand2 (x 4 4) (x 4 11)
    have b25345 := hb (x 4 11)
    have b25346 := hb (x 4 4 && x 4 11)
    clear * - r25344 b25345 b25346 d25327
    omega
  have d25347 : (x 4 6 && x 4 11).toNat = 0 := by
    have r25348 := hand2 (x 4 6) (x 4 11)
    have b25349 := hb (x 4 11)
    have b25350 := hb (x 4 6 && x 4 11)
    clear * - r25348 b25349 b25350 d25327
    omega
  have d25351 : (x 4 11 && x 4 12).toNat = 0 := by
    have r25352 := hand1 (x 4 11) (x 4 12)
    have b25353 := hb (x 4 11)
    have b25354 := hb (x 4 11 && x 4 12)
    clear * - r25352 b25353 b25354 d25327
    omega
  cases h25355 : x 0 8
  · have f25356 : (x 0 8).toNat = 0 := by rw [h25355]; rfl
    have d25357 : (x 0 8 && x 0 14).toNat = 0 := by
      have r25358 := hand1 (x 0 8) (x 0 14)
      have b25359 := hb (x 0 8)
      have b25360 := hb (x 0 8 && x 0 14)
      clear * - r25358 b25359 b25360 f25356
      omega
    have d25361 : (x 8 7).toNat = 1 := by
      have r25362 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25363 := hb (x 0 8)
      have b25364 := hb (x 8 7)
      have b25365 := hb (x 7 1 && x 7 8)
      have b25366 := hb (x 6 2 && x 6 9)
      have b25367 := hb (x 5 3 && x 5 10)
      have b25368 := hb (x 4 4 && x 4 11)
      have b25369 := hb (x 3 5 && x 3 12)
      have b25370 := hb (x 2 6 && x 2 13)
      have b25371 := hb (x 1 7 && x 1 14)
      clear * - r25362 b25363 b25364 b25365 b25366 b25367 b25368 b25369 b25370 b25371 d25259 d25287 d25315 d25343 g33 g34 g35 f25356
      omega
    have d25372 : (x 15 8).toNat = 0 := by
      have r25373 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25374 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e25375 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e25376 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e25377 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e25378 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e25379 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b25380 := hb (x 8 7)
      have b25381 := hb (x 9 6)
      have b25382 := hb (x 10 5)
      have b25383 := hb (x 11 4)
      have b25384 := hb (x 12 11)
      have b25385 := hb (x 13 10)
      have b25386 := hb (x 14 9)
      have b25387 := hb (x 15 8)
      clear * - r25373 e25374 e25375 e25376 e25377 e25378 e25379 b25380 b25381 b25382 b25383 b25384 b25385 b25386 b25387 d25361
      omega
    have d25388 : (x 15 1 && x 15 8).toNat = 0 := by
      have r25389 := hand2 (x 15 1) (x 15 8)
      have b25390 := hb (x 15 8)
      have b25391 := hb (x 15 1 && x 15 8)
      clear * - r25389 b25390 b25391 d25372
      omega
    have d25392 : (x 15 3 && x 15 8).toNat = 0 := by
      have r25393 := hand2 (x 15 3) (x 15 8)
      have b25394 := hb (x 15 8)
      have b25395 := hb (x 15 3 && x 15 8)
      clear * - r25393 b25394 b25395 d25372
      omega
    have d25396 : (x 14 9).toNat = 0 := by
      have r25397 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25398 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e25399 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e25400 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e25401 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e25402 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e25403 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b25404 := hb (x 8 7)
      have b25405 := hb (x 9 6)
      have b25406 := hb (x 10 5)
      have b25407 := hb (x 11 4)
      have b25408 := hb (x 12 11)
      have b25409 := hb (x 13 10)
      have b25410 := hb (x 14 9)
      have b25411 := hb (x 15 8)
      clear * - r25397 e25398 e25399 e25400 e25401 e25402 e25403 b25404 b25405 b25406 b25407 b25408 b25409 b25410 b25411 d25372 d25361
      omega
    have d25412 : (x 14 2 && x 14 9).toNat = 0 := by
      have r25413 := hand2 (x 14 2) (x 14 9)
      have b25414 := hb (x 14 9)
      have b25415 := hb (x 14 2 && x 14 9)
      clear * - r25413 b25414 b25415 d25396
      omega
    have d25416 : (x 14 4 && x 14 9).toNat = 0 := by
      have r25417 := hand2 (x 14 4) (x 14 9)
      have b25418 := hb (x 14 9)
      have b25419 := hb (x 14 4 && x 14 9)
      clear * - r25417 b25418 b25419 d25396
      omega
    have d25420 : (x 13 10).toNat = 0 := by
      have r25421 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25422 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e25423 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e25424 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e25425 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e25426 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e25427 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b25428 := hb (x 8 7)
      have b25429 := hb (x 9 6)
      have b25430 := hb (x 10 5)
      have b25431 := hb (x 11 4)
      have b25432 := hb (x 12 11)
      have b25433 := hb (x 13 10)
      have b25434 := hb (x 14 9)
      have b25435 := hb (x 15 8)
      clear * - r25421 e25422 e25423 e25424 e25425 e25426 e25427 b25428 b25429 b25430 b25431 b25432 b25433 b25434 b25435 d25372 d25396 d25361
      omega
    have d25436 : (x 13 3 && x 13 10).toNat = 0 := by
      have r25437 := hand2 (x 13 3) (x 13 10)
      have b25438 := hb (x 13 10)
      have b25439 := hb (x 13 3 && x 13 10)
      clear * - r25437 b25438 b25439 d25420
      omega
    have d25440 : (x 13 5 && x 13 10).toNat = 0 := by
      have r25441 := hand2 (x 13 5) (x 13 10)
      have b25442 := hb (x 13 10)
      have b25443 := hb (x 13 5 && x 13 10)
      clear * - r25441 b25442 b25443 d25420
      omega
    have d25444 : (x 12 11).toNat = 0 := by
      have r25445 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25446 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e25447 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e25448 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e25449 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e25450 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e25451 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b25452 := hb (x 8 7)
      have b25453 := hb (x 9 6)
      have b25454 := hb (x 10 5)
      have b25455 := hb (x 11 4)
      have b25456 := hb (x 12 11)
      have b25457 := hb (x 13 10)
      have b25458 := hb (x 14 9)
      have b25459 := hb (x 15 8)
      clear * - r25445 e25446 e25447 e25448 e25449 e25450 e25451 b25452 b25453 b25454 b25455 b25456 b25457 b25458 b25459 d25372 d25396 d25420 d25361
      omega
    have d25460 : (x 12 4 && x 12 11).toNat = 0 := by
      have r25461 := hand2 (x 12 4) (x 12 11)
      have b25462 := hb (x 12 11)
      have b25463 := hb (x 12 4 && x 12 11)
      clear * - r25461 b25462 b25463 d25444
      omega
    have d25464 : (x 12 6 && x 12 11).toNat = 0 := by
      have r25465 := hand2 (x 12 6) (x 12 11)
      have b25466 := hb (x 12 11)
      have b25467 := hb (x 12 6 && x 12 11)
      clear * - r25465 b25466 b25467 d25444
      omega
    have d25468 : (x 11 4).toNat = 0 := by
      have r25469 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25470 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e25471 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e25472 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e25473 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e25474 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e25475 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b25476 := hb (x 8 7)
      have b25477 := hb (x 9 6)
      have b25478 := hb (x 10 5)
      have b25479 := hb (x 11 4)
      have b25480 := hb (x 12 11)
      have b25481 := hb (x 13 10)
      have b25482 := hb (x 14 9)
      have b25483 := hb (x 15 8)
      clear * - r25469 e25470 e25471 e25472 e25473 e25474 e25475 b25476 b25477 b25478 b25479 b25480 b25481 b25482 b25483 d25372 d25396 d25420 d25444 d25361
      omega
    have d25484 : (x 11 4 && x 11 5).toNat = 0 := by
      have r25485 := hand1 (x 11 4) (x 11 5)
      have b25486 := hb (x 11 4)
      have b25487 := hb (x 11 4 && x 11 5)
      clear * - r25485 b25486 b25487 d25468
      omega
    have d25488 : (x 10 5).toNat = 0 := by
      have r25489 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25490 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e25491 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e25492 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e25493 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e25494 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e25495 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b25496 := hb (x 8 7)
      have b25497 := hb (x 9 6)
      have b25498 := hb (x 10 5)
      have b25499 := hb (x 11 4)
      have b25500 := hb (x 12 11)
      have b25501 := hb (x 13 10)
      have b25502 := hb (x 14 9)
      have b25503 := hb (x 15 8)
      clear * - r25489 e25490 e25491 e25492 e25493 e25494 e25495 b25496 b25497 b25498 b25499 b25500 b25501 b25502 b25503 d25372 d25396 d25420 d25444 d25468 d25361
      omega
    have d25504 : (x 10 5 && x 10 6).toNat = 0 := by
      have r25505 := hand1 (x 10 5) (x 10 6)
      have b25506 := hb (x 10 5)
      have b25507 := hb (x 10 5 && x 10 6)
      clear * - r25505 b25506 b25507 d25488
      omega
    have d25508 : (x 9 6).toNat = 0 := by
      have r25509 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25510 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
      have e25511 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
      have e25512 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
      have e25513 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
      have e25514 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
      have e25515 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
      have b25516 := hb (x 8 7)
      have b25517 := hb (x 9 6)
      have b25518 := hb (x 10 5)
      have b25519 := hb (x 11 4)
      have b25520 := hb (x 12 11)
      have b25521 := hb (x 13 10)
      have b25522 := hb (x 14 9)
      have b25523 := hb (x 15 8)
      clear * - r25509 e25510 e25511 e25512 e25513 e25514 e25515 b25516 b25517 b25518 b25519 b25520 b25521 b25522 b25523 d25372 d25396 d25420 d25444 d25468 d25488 d25361
      omega
    have d25524 : (x 9 1 && x 9 6).toNat = 0 := by
      have r25525 := hand2 (x 9 1) (x 9 6)
      have b25526 := hb (x 9 6)
      have b25527 := hb (x 9 1 && x 9 6)
      clear * - r25525 b25526 b25527 d25508
      omega
    have d25528 : (x 9 6 && x 9 7).toNat = 0 := by
      have r25529 := hand1 (x 9 6) (x 9 7)
      have b25530 := hb (x 9 6)
      have b25531 := hb (x 9 6 && x 9 7)
      clear * - r25529 b25530 b25531 d25508
      omega
    have d25532 : (x 8 2 && x 8 7).toNat = 1 := by
      have r25533 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := by have q := hcov5 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25534 := hb (x 0 10)
      have b25535 := hb (x 10 5)
      have b25536 := hb (x 9 1 && x 9 6)
      have b25537 := hb (x 8 2 && x 8 7)
      have b25538 := hb (x 7 3 && x 7 8)
      have b25539 := hb (x 6 4 && x 6 9)
      have b25540 := hb (x 5 5 && x 5 10)
      have b25541 := hb (x 4 6 && x 4 11)
      have b25542 := hb (x 3 7 && x 3 12)
      have b25543 := hb (x 2 8 && x 2 13)
      have b25544 := hb (x 1 9 && x 1 14)
      clear * - r25533 b25534 b25535 b25536 b25537 b25538 b25539 b25540 b25541 b25542 b25543 b25544 d25488 d25524 d25263 d25291 d25319 d25347 g23 g24 g25 g4
      omega
    have d25545 : (x 8 2).toNat = 1 := by
      have r25546 := hand1 (x 8 2) (x 8 7)
      have b25547 := hb (x 8 2)
      have b25548 := hb (x 8 2 && x 8 7)
      clear * - r25546 b25547 b25548 d25532
      omega
    have d25549 : (x 8 14).toNat = 1 := by
      have r25550 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
      have b25551 := hb (x 8 2)
      have b25552 := hb (x 8 14)
      clear * - r25550 b25551 b25552 d25545
      omega
    have d25553 : (x 7 1).toNat = 0 := by
      have r25554 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25555 := hb (x 7 1)
      have b25556 := hb (x 8 14)
      clear * - r25554 b25555 b25556 d25549
      omega
    have d25557 : (x 7 1 && x 7 14).toNat = 0 := by
      have r25558 := hand1 (x 7 1) (x 7 14)
      have b25559 := hb (x 7 1)
      have b25560 := hb (x 7 1 && x 7 14)
      clear * - r25558 b25559 b25560 d25553
      omega
    have d25561 : (x 7 1 && x 7 11).toNat = 0 := by
      have r25562 := hand1 (x 7 1) (x 7 11)
      have b25563 := hb (x 7 1)
      have b25564 := hb (x 7 1 && x 7 11)
      clear * - r25562 b25563 b25564 d25553
      omega
    have d25565 : (x 7 1 && x 7 7).toNat = 0 := by
      have r25566 := hand1 (x 7 1) (x 7 7)
      have b25567 := hb (x 7 1)
      have b25568 := hb (x 7 1 && x 7 7)
      clear * - r25566 b25567 b25568 d25553
      omega
    have d25569 : (x 8 6).toNat = 1 := by
      have r25570 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25571 := hb (x (-1) 9)
      have b25572 := hb (x 8 6)
      have b25573 := hb (x 7 1 && x 7 7)
      have b25574 := hb (x 6 2 && x 6 8)
      have b25575 := hb (x 5 3 && x 5 9)
      have b25576 := hb (x 4 4 && x 4 10)
      have b25577 := hb (x 3 5 && x 3 11)
      have b25578 := hb (x 2 6 && x 2 12)
      have b25579 := hb (x 1 7 && x 1 13)
      have b25580 := hb (x 0 8 && x 0 14)
      clear * - r25570 b25571 b25572 b25573 b25574 b25575 b25576 b25577 b25578 b25579 b25580 d25565 g26 g27 g28 g29 g30 g31 d25357 g2
      omega
    have d25581 : (x 14 8).toNat = 0 := by
      have r25582 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25583 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e25584 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e25585 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e25586 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e25587 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e25588 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b25589 := hb (x 7 7)
      have b25590 := hb (x 8 6)
      have b25591 := hb (x 9 5)
      have b25592 := hb (x 10 4)
      have b25593 := hb (x 11 11)
      have b25594 := hb (x 12 10)
      have b25595 := hb (x 13 9)
      have b25596 := hb (x 14 8)
      clear * - r25582 e25583 e25584 e25585 e25586 e25587 e25588 b25589 b25590 b25591 b25592 b25593 b25594 b25595 b25596 d25569
      omega
    have d25597 : (x 14 2 && x 14 8).toNat = 0 := by
      have r25598 := hand2 (x 14 2) (x 14 8)
      have b25599 := hb (x 14 8)
      have b25600 := hb (x 14 2 && x 14 8)
      clear * - r25598 b25599 b25600 d25581
      omega
    have d25601 : (x 13 9).toNat = 0 := by
      have r25602 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25603 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e25604 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e25605 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e25606 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e25607 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e25608 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b25609 := hb (x 7 7)
      have b25610 := hb (x 8 6)
      have b25611 := hb (x 9 5)
      have b25612 := hb (x 10 4)
      have b25613 := hb (x 11 11)
      have b25614 := hb (x 12 10)
      have b25615 := hb (x 13 9)
      have b25616 := hb (x 14 8)
      clear * - r25602 e25603 e25604 e25605 e25606 e25607 e25608 b25609 b25610 b25611 b25612 b25613 b25614 b25615 b25616 d25581 d25569
      omega
    have d25617 : (x 13 3 && x 13 9).toNat = 0 := by
      have r25618 := hand2 (x 13 3) (x 13 9)
      have b25619 := hb (x 13 9)
      have b25620 := hb (x 13 3 && x 13 9)
      clear * - r25618 b25619 b25620 d25601
      omega
    have d25621 : (x 12 10).toNat = 0 := by
      have r25622 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25623 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e25624 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e25625 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e25626 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e25627 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e25628 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b25629 := hb (x 7 7)
      have b25630 := hb (x 8 6)
      have b25631 := hb (x 9 5)
      have b25632 := hb (x 10 4)
      have b25633 := hb (x 11 11)
      have b25634 := hb (x 12 10)
      have b25635 := hb (x 13 9)
      have b25636 := hb (x 14 8)
      clear * - r25622 e25623 e25624 e25625 e25626 e25627 e25628 b25629 b25630 b25631 b25632 b25633 b25634 b25635 b25636 d25581 d25601 d25569
      omega
    have d25637 : (x 12 4 && x 12 10).toNat = 0 := by
      have r25638 := hand2 (x 12 4) (x 12 10)
      have b25639 := hb (x 12 10)
      have b25640 := hb (x 12 4 && x 12 10)
      clear * - r25638 b25639 b25640 d25621
      omega
    have d25641 : (x 11 11).toNat = 0 := by
      have r25642 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25643 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
      have e25644 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
      have e25645 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
      have e25646 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
      have e25647 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
      have e25648 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
      have b25649 := hb (x 7 7)
      have b25650 := hb (x 8 6)
      have b25651 := hb (x 9 5)
      have b25652 := hb (x 10 4)
      have b25653 := hb (x 11 11)
      have b25654 := hb (x 12 10)
      have b25655 := hb (x 13 9)
      have b25656 := hb (x 14 8)
      clear * - r25642 e25643 e25644 e25645 e25646 e25647 e25648 b25649 b25650 b25651 b25652 b25653 b25654 b25655 b25656 d25581 d25601 d25621 d25569
      omega
    have d25657 : (x 11 1 && x 11 11).toNat = 0 := by
      have r25658 := hand2 (x 11 1) (x 11 11)
      have b25659 := hb (x 11 11)
      have b25660 := hb (x 11 1 && x 11 11)
      clear * - r25658 b25659 b25660 d25641
      omega
    have d25661 : (x 11 5 && x 11 11).toNat = 0 := by
      have r25662 := hand2 (x 11 5) (x 11 11)
      have b25663 := hb (x 11 11)
      have b25664 := hb (x 11 5 && x 11 11)
      clear * - r25662 b25663 b25664 d25641
      omega
    have d25665 : (x 7 13).toNat = 0 := by
      have r25666 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
      have b25667 := hb (x 7 1)
      have b25668 := hb (x 7 13)
      clear * - r25666 b25667 b25668 d25553
      omega
    have d25669 : (x 7 5).toNat = 0 := by
      have r25670 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
      have b25671 := hb (x 7 5)
      have b25672 := hb (x 7 13)
      clear * - r25670 b25671 b25672 d25665
      omega
    have d25673 : (x 7 5 && x 7 11).toNat = 0 := by
      have r25674 := hand1 (x 7 5) (x 7 11)
      have b25675 := hb (x 7 5)
      have b25676 := hb (x 7 5 && x 7 11)
      clear * - r25674 b25675 b25676 d25669
      omega
    have d25677 : (x 7 9).toNat = 0 := by
      have r25678 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
      have b25679 := hb (x 7 1)
      have b25680 := hb (x 7 9)
      clear * - r25678 b25679 b25680 d25553
      omega
    have d25681 : (x 10 12).toNat = 0 := by
      have r25682 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25683 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e25684 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b25685 := hb (x 7 3)
      have b25686 := hb (x 8 2)
      have b25687 := hb (x 9 13)
      have b25688 := hb (x 10 12)
      clear * - r25682 e25683 e25684 b25685 b25686 b25687 b25688 d25545
      omega
    have d25689 : (x 10 1 && x 10 12).toNat = 0 := by
      have r25690 := hand2 (x 10 1) (x 10 12)
      have b25691 := hb (x 10 12)
      have b25692 := hb (x 10 1 && x 10 12)
      clear * - r25690 b25691 b25692 d25681
      omega
    have d25693 : (x 10 2 && x 10 12).toNat = 0 := by
      have r25694 := hand2 (x 10 2) (x 10 12)
      have b25695 := hb (x 10 12)
      have b25696 := hb (x 10 2 && x 10 12)
      clear * - r25694 b25695 b25696 d25681
      omega
    have d25697 : (x 10 6 && x 10 12).toNat = 0 := by
      have r25698 := hand2 (x 10 6) (x 10 12)
      have b25699 := hb (x 10 12)
      have b25700 := hb (x 10 6 && x 10 12)
      clear * - r25698 b25699 b25700 d25681
      omega
    have d25701 : (x 9 13).toNat = 0 := by
      have r25702 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25703 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e25704 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b25705 := hb (x 7 3)
      have b25706 := hb (x 8 2)
      have b25707 := hb (x 9 13)
      have b25708 := hb (x 10 12)
      clear * - r25702 e25703 e25704 b25705 b25706 b25707 b25708 d25681 d25545
      omega
    have d25709 : (x 9 2 && x 9 13).toNat = 0 := by
      have r25710 := hand2 (x 9 2) (x 9 13)
      have b25711 := hb (x 9 13)
      have b25712 := hb (x 9 2 && x 9 13)
      clear * - r25710 b25711 b25712 d25701
      omega
    have d25713 : (x 9 3 && x 9 13).toNat = 0 := by
      have r25714 := hand2 (x 9 3) (x 9 13)
      have b25715 := hb (x 9 13)
      have b25716 := hb (x 9 3 && x 9 13)
      clear * - r25714 b25715 b25716 d25701
      omega
    have d25717 : (x 8 4 && x 8 14).toNat = 1 := by
      have r25718 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := by have q := hcov10 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25719 := hb (x 7 5)
      have b25720 := hb (x 12 10)
      have b25721 := hb (x 11 1 && x 11 11)
      have b25722 := hb (x 10 2 && x 10 12)
      have b25723 := hb (x 9 3 && x 9 13)
      have b25724 := hb (x 8 4 && x 8 14)
      clear * - r25718 b25719 b25720 b25721 b25722 b25723 b25724 d25621 d25657 d25693 d25713 d25669
      omega
    have d25725 : (x 8 4).toNat = 1 := by
      have r25726 := hand1 (x 8 4) (x 8 14)
      have b25727 := hb (x 8 4)
      have b25728 := hb (x 8 4 && x 8 14)
      clear * - r25726 b25727 b25728 d25717
      omega
    have d25729 : (x 8 12).toNat = 1 := by
      have r25730 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
      have b25731 := hb (x 8 4)
      have b25732 := hb (x 8 12)
      clear * - r25730 b25731 b25732 d25725
      omega
    have d25733 : (x 6 2).toNat = 0 := by
      have r25734 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25735 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e25736 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b25737 := hb (x 5 3)
      have b25738 := hb (x 6 2)
      have b25739 := hb (x 7 13)
      have b25740 := hb (x 8 12)
      clear * - r25734 e25735 e25736 b25737 b25738 b25739 b25740 d25729 d25665
      omega
    have d25741 : (x 6 2 && x 6 12).toNat = 0 := by
      have r25742 := hand1 (x 6 2) (x 6 12)
      have b25743 := hb (x 6 2)
      have b25744 := hb (x 6 2 && x 6 12)
      clear * - r25742 b25743 b25744 d25733
      omega
    have d25745 : (x 6 10).toNat = 0 := by
      have r25746 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
      have b25747 := hb (x 6 2)
      have b25748 := hb (x 6 10)
      clear * - r25746 b25747 b25748 d25733
      omega
    have d25749 : (x 6 1 && x 6 10).toNat = 0 := by
      have r25750 := hand2 (x 6 1) (x 6 10)
      have b25751 := hb (x 6 10)
      have b25752 := hb (x 6 1 && x 6 10)
      clear * - r25750 b25751 b25752 d25745
      omega
    have d25753 : (x 8 13).toNat = 1 := by
      have r25754 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25755 := hb (x 6 2)
      have b25756 := hb (x 8 13)
      have b25757 := hb (x 7 1 && x 7 14)
      clear * - r25754 b25755 b25756 b25757 d25557 d25733
      omega
    have d25758 : (x 8 1).toNat = 1 := by
      have r25759 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
      have b25760 := hb (x 8 1)
      have b25761 := hb (x 8 13)
      clear * - r25759 b25760 b25761 d25753
      omega
    have d25762 : (x 9 14).toNat = 0 := by
      have r25763 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25764 := hb (x 8 1)
      have b25765 := hb (x 9 14)
      clear * - r25763 b25764 b25765 d25758
      omega
    have d25766 : (x 9 7 && x 9 14).toNat = 0 := by
      have r25767 := hand2 (x 9 7) (x 9 14)
      have b25768 := hb (x 9 14)
      have b25769 := hb (x 9 7 && x 9 14)
      clear * - r25767 b25768 b25769 d25762
      omega
    have d25770 : (x 9 9 && x 9 14).toNat = 0 := by
      have r25771 := hand2 (x 9 9) (x 9 14)
      have b25772 := hb (x 9 14)
      have b25773 := hb (x 9 9 && x 9 14)
      clear * - r25771 b25772 b25773 d25762
      omega
    have d25774 : (x 9 2).toNat = 0 := by
      have r25775 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
      have b25776 := hb (x 9 2)
      have b25777 := hb (x 9 14)
      clear * - r25775 b25776 b25777 d25762
      omega
    have d25778 : (x 9 2 && x 9 9).toNat = 0 := by
      have r25779 := hand1 (x 9 2) (x 9 9)
      have b25780 := hb (x 9 2)
      have b25781 := hb (x 9 2 && x 9 9)
      clear * - r25779 b25780 b25781 d25774
      omega
    have d25782 : (x 9 12).toNat = 0 := by
      have r25783 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25784 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e25785 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b25786 := hb (x 6 3)
      have b25787 := hb (x 7 2)
      have b25788 := hb (x 8 13)
      have b25789 := hb (x 9 12)
      clear * - r25783 e25784 e25785 b25786 b25787 b25788 b25789 d25753
      omega
    have d25790 : (x 7 2).toNat = 0 := by
      have r25791 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25792 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e25793 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b25794 := hb (x 6 3)
      have b25795 := hb (x 7 2)
      have b25796 := hb (x 8 13)
      have b25797 := hb (x 9 12)
      clear * - r25791 e25792 e25793 b25794 b25795 b25796 b25797 d25782 d25753
      omega
    have d25798 : (x 7 10).toNat = 0 := by
      have r25799 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
      have b25800 := hb (x 7 2)
      have b25801 := hb (x 7 10)
      clear * - r25799 b25800 b25801 d25790
      omega
    have d25802 : (x 6 3).toNat = 0 := by
      have r25803 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25804 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e25805 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b25806 := hb (x 6 3)
      have b25807 := hb (x 7 2)
      have b25808 := hb (x 8 13)
      have b25809 := hb (x 9 12)
      clear * - r25803 e25804 e25805 b25806 b25807 b25808 b25809 d25782 d25753 d25790
      omega
    have d25810 : (x 6 11).toNat = 0 := by
      have r25811 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
      have b25812 := hb (x 6 3)
      have b25813 := hb (x 6 11)
      clear * - r25811 b25812 b25813 d25802
      omega
    have d25814 : (x 6 1 && x 6 11).toNat = 0 := by
      have r25815 := hand2 (x 6 1) (x 6 11)
      have b25816 := hb (x 6 11)
      have b25817 := hb (x 6 1 && x 6 11)
      clear * - r25815 b25816 b25817 d25810
      omega
    have d25818 : (x 5 3).toNat = 0 := by
      have r25819 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25820 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e25821 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b25822 := hb (x 5 3)
      have b25823 := hb (x 6 2)
      have b25824 := hb (x 7 13)
      have b25825 := hb (x 8 12)
      clear * - r25819 e25820 e25821 b25822 b25823 b25824 b25825 d25729 d25665 d25733
      omega
    have d25826 : (x 5 3 && x 5 13).toNat = 0 := by
      have r25827 := hand1 (x 5 3) (x 5 13)
      have b25828 := hb (x 5 3)
      have b25829 := hb (x 5 3 && x 5 13)
      clear * - r25827 b25828 b25829 d25818
      omega
    have d25830 : (x 5 11).toNat = 0 := by
      have r25831 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
      have b25832 := hb (x 5 3)
      have b25833 := hb (x 5 11)
      clear * - r25831 b25832 b25833 d25818
      omega
    have d25834 : (x 5 1 && x 5 11).toNat = 0 := by
      have r25835 := hand2 (x 5 1) (x 5 11)
      have b25836 := hb (x 5 11)
      have b25837 := hb (x 5 1 && x 5 11)
      clear * - r25835 b25836 b25837 d25830
      omega
    have d25838 : (x 5 2 && x 5 11).toNat = 0 := by
      have r25839 := hand2 (x 5 2) (x 5 11)
      have b25840 := hb (x 5 11)
      have b25841 := hb (x 5 2 && x 5 11)
      clear * - r25839 b25840 b25841 d25830
      omega
    have d25842 : (x 4 3 && x 4 12).toNat = 1 := by
      have r25843 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25844 := hb (x 1 6)
      have b25845 := hb (x 7 9)
      have b25846 := hb (x 6 1 && x 6 10)
      have b25847 := hb (x 5 2 && x 5 11)
      have b25848 := hb (x 4 3 && x 4 12)
      have b25849 := hb (x 3 4 && x 3 13)
      have b25850 := hb (x 2 5 && x 2 14)
      clear * - r25843 b25844 b25845 b25846 b25847 b25848 b25849 b25850 d25677 d25749 d25838 g36 g37 g8
      omega
    have d25851 : (x 4 12).toNat = 1 := by
      have r25852 := hand2 (x 4 3) (x 4 12)
      have b25853 := hb (x 4 12)
      have b25854 := hb (x 4 3 && x 4 12)
      clear * - r25852 b25853 b25854 d25842
      omega
    have d25855 : (x 3 13).toNat = 0 := by
      have r25856 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25857 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e25858 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b25859 := hb (x 1 3)
      have b25860 := hb (x 2 2)
      have b25861 := hb (x 3 13)
      have b25862 := hb (x 4 12)
      clear * - r25856 e25857 e25858 b25859 b25860 b25861 b25862 d25851
      omega
    have d25863 : (x 3 3 && x 3 13).toNat = 0 := by
      have r25864 := hand2 (x 3 3) (x 3 13)
      have b25865 := hb (x 3 13)
      have b25866 := hb (x 3 3 && x 3 13)
      clear * - r25864 b25865 b25866 d25855
      omega
    have d25867 : (x 4 2 && x 4 12).toNat = 1 := by
      have r25868 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25869 := hb (x 1 5)
      have b25870 := hb (x 6 10)
      have b25871 := hb (x 5 1 && x 5 11)
      have b25872 := hb (x 4 2 && x 4 12)
      have b25873 := hb (x 3 3 && x 3 13)
      have b25874 := hb (x 2 4 && x 2 14)
      clear * - r25868 b25869 b25870 b25871 b25872 b25873 b25874 d25745 d25834 d25863 g41 g7
      omega
    have d25875 : (x 4 2).toNat = 1 := by
      have r25876 := hand1 (x 4 2) (x 4 12)
      have b25877 := hb (x 4 2)
      have b25878 := hb (x 4 2 && x 4 12)
      clear * - r25876 b25877 b25878 d25867
      omega
    have d25879 : (x 6 12).toNat = 0 := by
      have r25880 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25881 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e25882 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b25883 := hb (x 3 3)
      have b25884 := hb (x 4 2)
      have b25885 := hb (x 5 13)
      have b25886 := hb (x 6 12)
      clear * - r25880 e25881 e25882 b25883 b25884 b25885 b25886 d25875
      omega
    have d25887 : (x 6 5 && x 6 12).toNat = 0 := by
      have r25888 := hand2 (x 6 5) (x 6 12)
      have b25889 := hb (x 6 12)
      have b25890 := hb (x 6 5 && x 6 12)
      clear * - r25888 b25889 b25890 d25879
      omega
    have d25891 : (x 6 6 && x 6 12).toNat = 0 := by
      have r25892 := hand2 (x 6 6) (x 6 12)
      have b25893 := hb (x 6 12)
      have b25894 := hb (x 6 6 && x 6 12)
      clear * - r25892 b25893 b25894 d25879
      omega
    have d25895 : (x 6 4).toNat = 0 := by
      have r25896 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
      have b25897 := hb (x 6 4)
      have b25898 := hb (x 6 12)
      clear * - r25896 b25897 b25898 d25879
      omega
    have d25899 : (x 6 1 && x 6 4).toNat = 0 := by
      have r25900 := hand2 (x 6 1) (x 6 4)
      have b25901 := hb (x 6 4)
      have b25902 := hb (x 6 1 && x 6 4)
      clear * - r25900 b25901 b25902 d25895
      omega
    have d25903 : (x 5 13).toNat = 0 := by
      have r25904 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25905 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e25906 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b25907 := hb (x 3 3)
      have b25908 := hb (x 4 2)
      have b25909 := hb (x 5 13)
      have b25910 := hb (x 6 12)
      clear * - r25904 e25905 e25906 b25907 b25908 b25909 b25910 d25879 d25875
      omega
    have d25911 : (x 5 6 && x 5 13).toNat = 0 := by
      have r25912 := hand2 (x 5 6) (x 5 13)
      have b25913 := hb (x 5 13)
      have b25914 := hb (x 5 6 && x 5 13)
      clear * - r25912 b25913 b25914 d25903
      omega
    have d25915 : (x 5 7 && x 5 13).toNat = 0 := by
      have r25916 := hand2 (x 5 7) (x 5 13)
      have b25917 := hb (x 5 13)
      have b25918 := hb (x 5 7 && x 5 13)
      clear * - r25916 b25917 b25918 d25903
      omega
    have d25919 : (x 5 5).toNat = 0 := by
      have r25920 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
      have b25921 := hb (x 5 5)
      have b25922 := hb (x 5 13)
      clear * - r25920 b25921 b25922 d25903
      omega
    have d25923 : (x 5 2 && x 5 5).toNat = 0 := by
      have r25924 := hand2 (x 5 2) (x 5 5)
      have b25925 := hb (x 5 5)
      have b25926 := hb (x 5 2 && x 5 5)
      clear * - r25924 b25925 b25926 d25919
      omega
    have d25927 : (x 3 5).toNat = 0 := by
      have r25928 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
      have b25929 := hb (x 3 5)
      have b25930 := hb (x 3 13)
      clear * - r25928 b25929 b25930 d25855
      omega
    have d25931 : (x 2 1 && x 2 14).toNat = 1 := by
      have r25932 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25933 := hb (x 1 2)
      have b25934 := hb (x 3 13)
      have b25935 := hb (x 2 1 && x 2 14)
      clear * - r25932 b25933 b25934 b25935 d25855 g6
      omega
    have d25936 : (x 2 1).toNat = 1 := by
      have r25937 := hand1 (x 2 1) (x 2 14)
      have b25938 := hb (x 2 1)
      have b25939 := hb (x 2 1 && x 2 14)
      clear * - r25937 b25938 b25939 d25931
      omega
    have d25940 : (x 3 14).toNat = 0 := by
      have r25941 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25942 := hb (x 2 1)
      have b25943 := hb (x 3 14)
      clear * - r25941 b25942 b25943 d25936
      omega
    have d25944 : (x 3 2).toNat = 0 := by
      have r25945 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b25946 := hb (x 3 2)
      have b25947 := hb (x 3 14)
      clear * - r25945 b25946 b25947 d25940
      omega
    have d25948 : (x 4 1 && x 4 14).toNat = 1 := by
      have r25949 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25950 := hb (x 3 2)
      have b25951 := hb (x 5 13)
      have b25952 := hb (x 4 1 && x 4 14)
      clear * - r25949 b25950 b25951 b25952 d25903 d25944
      omega
    have d25953 : (x 4 1).toNat = 1 := by
      have r25954 := hand1 (x 4 1) (x 4 14)
      have b25955 := hb (x 4 1)
      have b25956 := hb (x 4 1 && x 4 14)
      clear * - r25954 b25955 b25956 d25948
      omega
    have d25957 : (x 5 14).toNat = 0 := by
      have r25958 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25959 := hb (x 4 1)
      have b25960 := hb (x 5 14)
      clear * - r25958 b25959 b25960 d25953
      omega
    have d25961 : (x 5 6).toNat = 0 := by
      have r25962 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
      have b25963 := hb (x 5 6)
      have b25964 := hb (x 5 14)
      clear * - r25962 b25963 b25964 d25957
      omega
    have d25965 : (x 5 2).toNat = 0 := by
      have r25966 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
      have b25967 := hb (x 5 2)
      have b25968 := hb (x 5 14)
      clear * - r25966 b25967 b25968 d25957
      omega
    have d25969 : (x 5 2 && x 5 12).toNat = 0 := by
      have r25970 := hand1 (x 5 2) (x 5 12)
      have b25971 := hb (x 5 2)
      have b25972 := hb (x 5 2 && x 5 12)
      clear * - r25970 b25971 b25972 d25965
      omega
    have d25973 : (x 4 3 && x 4 13).toNat = 1 := by
      have r25974 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25975 := hb (x 2 5)
      have b25976 := hb (x 7 10)
      have b25977 := hb (x 6 1 && x 6 11)
      have b25978 := hb (x 5 2 && x 5 12)
      have b25979 := hb (x 4 3 && x 4 13)
      have b25980 := hb (x 3 4 && x 3 14)
      clear * - r25974 b25975 b25976 b25977 b25978 b25979 b25980 d25798 d25814 d25969 g42 g11
      omega
    have d25981 : (x 4 3).toNat = 1 := by
      have r25982 := hand1 (x 4 3) (x 4 13)
      have b25983 := hb (x 4 3)
      have b25984 := hb (x 4 3 && x 4 13)
      clear * - r25982 b25983 b25984 d25973
      omega
    have d25985 : (x 6 1 && x 6 14).toNat = 1 := by
      have r25986 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b25987 := hb (x 5 2)
      have b25988 := hb (x 7 13)
      have b25989 := hb (x 6 1 && x 6 14)
      clear * - r25986 b25987 b25988 b25989 d25665 d25965
      omega
    have d25990 : (x 6 1).toNat = 1 := by
      have r25991 := hand1 (x 6 1) (x 6 14)
      have b25992 := hb (x 6 1)
      have b25993 := hb (x 6 1 && x 6 14)
      clear * - r25991 b25992 b25993 d25985
      omega
    have d25994 : (x 7 12).toNat = 0 := by
      have r25995 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e25996 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e25997 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b25998 := hb (x 4 3)
      have b25999 := hb (x 5 2)
      have b26000 := hb (x 6 13)
      have b26001 := hb (x 7 12)
      clear * - r25995 e25996 e25997 b25998 b25999 b26000 b26001 d25965 d25981
      omega
    have d26002 : (x 7 4).toNat = 0 := by
      have r26003 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
      have b26004 := hb (x 7 4)
      have b26005 := hb (x 7 12)
      clear * - r26003 b26004 b26005 d25994
      omega
    have d26006 : (x 7 4 && x 7 11).toNat = 0 := by
      have r26007 := hand1 (x 7 4) (x 7 11)
      have b26008 := hb (x 7 4)
      have b26009 := hb (x 7 4 && x 7 11)
      clear * - r26007 b26008 b26009 d26002
      omega
    have d26010 : (x 8 3 && x 8 14).toNat = 1 := by
      have r26011 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26012 := hb (x 7 4)
      have b26013 := hb (x 11 11)
      have b26014 := hb (x 10 1 && x 10 12)
      have b26015 := hb (x 9 2 && x 9 13)
      have b26016 := hb (x 8 3 && x 8 14)
      clear * - r26011 b26012 b26013 b26014 b26015 b26016 d25641 d25689 d25709 d26002
      omega
    have d26017 : (x 8 3).toNat = 1 := by
      have r26018 := hand1 (x 8 3) (x 8 14)
      have b26019 := hb (x 8 3)
      have b26020 := hb (x 8 3 && x 8 14)
      clear * - r26018 b26019 b26020 d26010
      omega
    have d26021 : (x 11 12).toNat = 0 := by
      have r26022 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26023 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e26024 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b26025 := hb (x 8 3)
      have b26026 := hb (x 9 2)
      have b26027 := hb (x 10 13)
      have b26028 := hb (x 11 12)
      clear * - r26022 e26023 e26024 b26025 b26026 b26027 b26028 d25774 d26017
      omega
    have d26029 : (x 11 5 && x 11 12).toNat = 0 := by
      have r26030 := hand2 (x 11 5) (x 11 12)
      have b26031 := hb (x 11 12)
      have b26032 := hb (x 11 5 && x 11 12)
      clear * - r26030 b26031 b26032 d26021
      omega
    have d26033 : (x 11 7 && x 11 12).toNat = 0 := by
      have r26034 := hand2 (x 11 7) (x 11 12)
      have b26035 := hb (x 11 12)
      have b26036 := hb (x 11 7 && x 11 12)
      clear * - r26034 b26035 b26036 d26021
      omega
    have d26037 : (x 10 13).toNat = 0 := by
      have r26038 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26039 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e26040 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b26041 := hb (x 8 3)
      have b26042 := hb (x 9 2)
      have b26043 := hb (x 10 13)
      have b26044 := hb (x 11 12)
      clear * - r26038 e26039 e26040 b26041 b26042 b26043 b26044 d26021 d25774 d26017
      omega
    have d26045 : (x 10 6 && x 10 13).toNat = 0 := by
      have r26046 := hand2 (x 10 6) (x 10 13)
      have b26047 := hb (x 10 13)
      have b26048 := hb (x 10 6 && x 10 13)
      clear * - r26046 b26047 b26048 d26037
      omega
    have d26049 : (x 10 8 && x 10 13).toNat = 0 := by
      have r26050 := hand2 (x 10 8) (x 10 13)
      have b26051 := hb (x 10 13)
      have b26052 := hb (x 10 8 && x 10 13)
      clear * - r26050 b26051 b26052 d26037
      omega
    have d26053 : (x 6 13).toNat = 0 := by
      have r26054 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26055 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e26056 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b26057 := hb (x 4 3)
      have b26058 := hb (x 5 2)
      have b26059 := hb (x 6 13)
      have b26060 := hb (x 7 12)
      clear * - r26054 e26055 e26056 b26057 b26058 b26059 b26060 d25994 d25965 d25981
      omega
    have d26061 : (x 6 5).toNat = 0 := by
      have r26062 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
      have b26063 := hb (x 6 5)
      have b26064 := hb (x 6 13)
      clear * - r26062 b26063 b26064 d26053
      omega
    have d26065 : (x 9 7 && x 9 13).toNat = 0 := by
      have r26066 := hand2 (x 9 7) (x 9 13)
      have b26067 := hb (x 9 13)
      have b26068 := hb (x 9 7 && x 9 13)
      clear * - r26066 b26067 b26068 d25701
      omega
    have d26069 : (x 7 3).toNat = 0 := by
      have r26070 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26071 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e26072 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b26073 := hb (x 7 3)
      have b26074 := hb (x 8 2)
      have b26075 := hb (x 9 13)
      have b26076 := hb (x 10 12)
      clear * - r26070 e26071 e26072 b26073 b26074 b26075 b26076 d25681 d25701 d25545
      omega
    have d26077 : (x 7 11).toNat = 0 := by
      have r26078 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
      have b26079 := hb (x 7 3)
      have b26080 := hb (x 7 11)
      clear * - r26078 b26079 b26080 d26069
      omega
    have d26081 : (x (-1) 8).toNat = 0 := by
      have r26082 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26083 := hb (x (-7) 14)
      have b26084 := hb (x (-6) 13)
      have b26085 := hb (x (-5) 12)
      have b26086 := hb (x (-4) 11)
      have b26087 := hb (x (-3) 10)
      have b26088 := hb (x (-2) 9)
      have b26089 := hb (x (-1) 8)
      have b26090 := hb (x 0 7)
      have b26091 := hb (x 1 6)
      have b26092 := hb (x 2 5)
      have b26093 := hb (x 3 4)
      have b26094 := hb (x 4 3)
      have b26095 := hb (x 5 2)
      have b26096 := hb (x 6 1)
      clear * - r26082 b26083 b26084 b26085 b26086 b26087 b26088 b26089 b26090 b26091 b26092 b26093 b26094 b26095 b26096 d25990 d25965 d25981 g13 g11 g8 g3
      omega
    have d26097 : (x (-2) 9).toNat = 0 := by
      have r26098 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26099 := hb (x (-7) 14)
      have b26100 := hb (x (-6) 13)
      have b26101 := hb (x (-5) 12)
      have b26102 := hb (x (-4) 11)
      have b26103 := hb (x (-3) 10)
      have b26104 := hb (x (-2) 9)
      have b26105 := hb (x (-1) 8)
      have b26106 := hb (x 0 7)
      have b26107 := hb (x 1 6)
      have b26108 := hb (x 2 5)
      have b26109 := hb (x 3 4)
      have b26110 := hb (x 4 3)
      have b26111 := hb (x 5 2)
      have b26112 := hb (x 6 1)
      clear * - r26098 b26099 b26100 b26101 b26102 b26103 b26104 b26105 b26106 b26107 b26108 b26109 b26110 b26111 b26112 d25990 d25965 d25981 g13 g11 g8 g3 d26081
      omega
    have d26113 : (x (-2) 9 && x (-2) 12).toNat = 0 := by
      have r26114 := hand1 (x (-2) 9) (x (-2) 12)
      have b26115 := hb (x (-2) 9)
      have b26116 := hb (x (-2) 9 && x (-2) 12)
      clear * - r26114 b26115 b26116 d26097
      omega
    have d26117 : (x (-3) 10).toNat = 0 := by
      have r26118 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26119 := hb (x (-7) 14)
      have b26120 := hb (x (-6) 13)
      have b26121 := hb (x (-5) 12)
      have b26122 := hb (x (-4) 11)
      have b26123 := hb (x (-3) 10)
      have b26124 := hb (x (-2) 9)
      have b26125 := hb (x (-1) 8)
      have b26126 := hb (x 0 7)
      have b26127 := hb (x 1 6)
      have b26128 := hb (x 2 5)
      have b26129 := hb (x 3 4)
      have b26130 := hb (x 4 3)
      have b26131 := hb (x 5 2)
      have b26132 := hb (x 6 1)
      clear * - r26118 b26119 b26120 b26121 b26122 b26123 b26124 b26125 b26126 b26127 b26128 b26129 b26130 b26131 b26132 d25990 d25965 d25981 g13 g11 g8 g3 d26081 d26097
      omega
    have d26133 : (x (-3) 10 && x (-3) 13).toNat = 0 := by
      have r26134 := hand1 (x (-3) 10) (x (-3) 13)
      have b26135 := hb (x (-3) 10)
      have b26136 := hb (x (-3) 10 && x (-3) 13)
      clear * - r26134 b26135 b26136 d26117
      omega
    have d26137 : (x (-4) 11).toNat = 0 := by
      have r26138 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26139 := hb (x (-7) 14)
      have b26140 := hb (x (-6) 13)
      have b26141 := hb (x (-5) 12)
      have b26142 := hb (x (-4) 11)
      have b26143 := hb (x (-3) 10)
      have b26144 := hb (x (-2) 9)
      have b26145 := hb (x (-1) 8)
      have b26146 := hb (x 0 7)
      have b26147 := hb (x 1 6)
      have b26148 := hb (x 2 5)
      have b26149 := hb (x 3 4)
      have b26150 := hb (x 4 3)
      have b26151 := hb (x 5 2)
      have b26152 := hb (x 6 1)
      clear * - r26138 b26139 b26140 b26141 b26142 b26143 b26144 b26145 b26146 b26147 b26148 b26149 b26150 b26151 b26152 d25990 d25965 d25981 g13 g11 g8 g3 d26081 d26097 d26117
      omega
    have d26153 : (x (-4) 11 && x (-4) 14).toNat = 0 := by
      have r26154 := hand1 (x (-4) 11) (x (-4) 14)
      have b26155 := hb (x (-4) 11)
      have b26156 := hb (x (-4) 11 && x (-4) 14)
      clear * - r26154 b26155 b26156 d26137
      omega
    have d26157 : (x (-5) 12).toNat = 0 := by
      have r26158 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26159 := hb (x (-7) 14)
      have b26160 := hb (x (-6) 13)
      have b26161 := hb (x (-5) 12)
      have b26162 := hb (x (-4) 11)
      have b26163 := hb (x (-3) 10)
      have b26164 := hb (x (-2) 9)
      have b26165 := hb (x (-1) 8)
      have b26166 := hb (x 0 7)
      have b26167 := hb (x 1 6)
      have b26168 := hb (x 2 5)
      have b26169 := hb (x 3 4)
      have b26170 := hb (x 4 3)
      have b26171 := hb (x 5 2)
      have b26172 := hb (x 6 1)
      clear * - r26158 b26159 b26160 b26161 b26162 b26163 b26164 b26165 b26166 b26167 b26168 b26169 b26170 b26171 b26172 d25990 d25965 d25981 g13 g11 g8 g3 d26081 d26097 d26117 d26137
      omega
    have d26173 : (x 4 3 && x 4 6).toNat = 1 := by
      have r26174 : 1 ≤ (x 7 3).toNat + (x 6 1 && x 6 4).toNat + (x 5 2 && x 5 5).toNat + (x 4 3 && x 4 6).toNat + (x 3 4 && x 3 7).toNat + (x 2 5 && x 2 8).toNat + (x 1 6 && x 1 9).toNat + (x 0 7 && x 0 10).toNat + (x (-1) 8 && x (-1) 11).toNat + (x (-2) 9 && x (-2) 12).toNat + (x (-3) 10 && x (-3) 13).toNat + (x (-4) 11 && x (-4) 14).toNat + (x (-5) 12).toNat := by have q := hcov3 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26175 := hb (x (-5) 12)
      have b26176 := hb (x 7 3)
      have b26177 := hb (x 6 1 && x 6 4)
      have b26178 := hb (x 5 2 && x 5 5)
      have b26179 := hb (x 4 3 && x 4 6)
      have b26180 := hb (x 3 4 && x 3 7)
      have b26181 := hb (x 2 5 && x 2 8)
      have b26182 := hb (x 1 6 && x 1 9)
      have b26183 := hb (x 0 7 && x 0 10)
      have b26184 := hb (x (-1) 8 && x (-1) 11)
      have b26185 := hb (x (-2) 9 && x (-2) 12)
      have b26186 := hb (x (-3) 10 && x (-3) 13)
      have b26187 := hb (x (-4) 11 && x (-4) 14)
      clear * - r26174 b26175 b26176 b26177 b26178 b26179 b26180 b26181 b26182 b26183 b26184 b26185 b26186 b26187 d26069 d25899 d25923 g18 g19 g20 g21 g22 d26113 d26133 d26153 d26157
      omega
    have d26188 : (x 4 6).toNat = 1 := by
      have r26189 := hand2 (x 4 3) (x 4 6)
      have b26190 := hb (x 4 6)
      have b26191 := hb (x 4 3 && x 4 6)
      clear * - r26189 b26190 b26191 d26173
      omega
    have d26192 : (x 10 8).toNat = 0 := by
      have r26193 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26194 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e26195 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e26196 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e26197 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e26198 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e26199 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b26200 := hb (x 3 7)
      have b26201 := hb (x 4 6)
      have b26202 := hb (x 5 5)
      have b26203 := hb (x 6 4)
      have b26204 := hb (x 7 11)
      have b26205 := hb (x 8 10)
      have b26206 := hb (x 9 9)
      have b26207 := hb (x 10 8)
      clear * - r26193 e26194 e26195 e26196 e26197 e26198 e26199 b26200 b26201 b26202 b26203 b26204 b26205 b26206 b26207 d26077 d25895 d25919 d26188
      omega
    have d26208 : (x 10 1 && x 10 8).toNat = 0 := by
      have r26209 := hand2 (x 10 1) (x 10 8)
      have b26210 := hb (x 10 8)
      have b26211 := hb (x 10 1 && x 10 8)
      clear * - r26209 b26210 b26211 d26192
      omega
    have d26212 : (x 10 2 && x 10 8).toNat = 0 := by
      have r26213 := hand2 (x 10 2) (x 10 8)
      have b26214 := hb (x 10 8)
      have b26215 := hb (x 10 2 && x 10 8)
      clear * - r26213 b26214 b26215 d26192
      omega
    have d26216 : (x 9 9).toNat = 0 := by
      have r26217 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26218 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e26219 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e26220 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e26221 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e26222 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e26223 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b26224 := hb (x 3 7)
      have b26225 := hb (x 4 6)
      have b26226 := hb (x 5 5)
      have b26227 := hb (x 6 4)
      have b26228 := hb (x 7 11)
      have b26229 := hb (x 8 10)
      have b26230 := hb (x 9 9)
      have b26231 := hb (x 10 8)
      clear * - r26217 e26218 e26219 e26220 e26221 e26222 e26223 b26224 b26225 b26226 b26227 b26228 b26229 b26230 b26231 d26192 d26077 d25895 d25919 d26188
      omega
    have d26232 : (x 9 3 && x 9 9).toNat = 0 := by
      have r26233 := hand2 (x 9 3) (x 9 9)
      have b26234 := hb (x 9 9)
      have b26235 := hb (x 9 3 && x 9 9)
      clear * - r26233 b26234 b26235 d26216
      omega
    have d26236 : (x 8 10).toNat = 0 := by
      have r26237 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26238 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e26239 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e26240 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e26241 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e26242 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e26243 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have b26244 := hb (x 3 7)
      have b26245 := hb (x 4 6)
      have b26246 := hb (x 5 5)
      have b26247 := hb (x 6 4)
      have b26248 := hb (x 7 11)
      have b26249 := hb (x 8 10)
      have b26250 := hb (x 9 9)
      have b26251 := hb (x 10 8)
      clear * - r26237 e26238 e26239 e26240 e26241 e26242 e26243 b26244 b26245 b26246 b26247 b26248 b26249 b26250 b26251 d26192 d26216 d26077 d25895 d25919 d26188
      omega
    have d26252 : (x 8 3 && x 8 10).toNat = 0 := by
      have r26253 := hand2 (x 8 3) (x 8 10)
      have b26254 := hb (x 8 10)
      have b26255 := hb (x 8 3 && x 8 10)
      clear * - r26253 b26254 b26255 d26236
      omega
    have d26256 : (x 8 4 && x 8 10).toNat = 0 := by
      have r26257 := hand2 (x 8 4) (x 8 10)
      have b26258 := hb (x 8 10)
      have b26259 := hb (x 8 4 && x 8 10)
      clear * - r26257 b26258 b26259 d26236
      omega
    have d26260 : (x 4 4 && x 4 14).toNat = 1 := by
      have r26261 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26262 := hb (x 3 5)
      have b26263 := hb (x 8 10)
      have b26264 := hb (x 7 1 && x 7 11)
      have b26265 := hb (x 6 2 && x 6 12)
      have b26266 := hb (x 5 3 && x 5 13)
      have b26267 := hb (x 4 4 && x 4 14)
      clear * - r26261 b26262 b26263 b26264 b26265 b26266 b26267 d26236 d25561 d25741 d25826 d25927
      omega
    have d26268 : (x 4 4).toNat = 1 := by
      have r26269 := hand1 (x 4 4) (x 4 14)
      have b26270 := hb (x 4 4)
      have b26271 := hb (x 4 4 && x 4 14)
      clear * - r26269 b26270 b26271 d26260
      omega
    have d26272 : (x 8 8).toNat = 0 := by
      have r26273 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26274 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e26275 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e26276 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e26277 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e26278 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e26279 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b26280 := hb (x 1 7)
      have b26281 := hb (x 2 6)
      have b26282 := hb (x 3 5)
      have b26283 := hb (x 4 4)
      have b26284 := hb (x 5 11)
      have b26285 := hb (x 6 10)
      have b26286 := hb (x 7 9)
      have b26287 := hb (x 8 8)
      clear * - r26273 e26274 e26275 e26276 e26277 e26278 e26279 b26280 b26281 b26282 b26283 b26284 b26285 b26286 b26287 d25677 d25745 d25830 d26268 d25927
      omega
    have d26288 : (x 8 8 && x 8 14).toNat = 0 := by
      have r26289 := hand1 (x 8 8) (x 8 14)
      have b26290 := hb (x 8 8)
      have b26291 := hb (x 8 8 && x 8 14)
      clear * - r26289 b26290 b26291 d26272
      omega
    have d26292 : (x 8 7 && x 8 8).toNat = 0 := by
      have r26293 := hand2 (x 8 7) (x 8 8)
      have b26294 := hb (x 8 8)
      have b26295 := hb (x 8 7 && x 8 8)
      clear * - r26293 b26294 b26295 d26272
      omega
    have d26296 : (x 16 7).toNat = 1 := by
      have r26297 : 1 ≤ (x 16 7).toNat + (x 15 1 && x 15 8).toNat + (x 14 2 && x 14 9).toNat + (x 13 3 && x 13 10).toNat + (x 12 4 && x 12 11).toNat + (x 11 5 && x 11 12).toNat + (x 10 6 && x 10 13).toNat + (x 9 7 && x 9 14).toNat + (x 8 8).toNat := by have q := hcov7 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26298 := hb (x 8 8)
      have b26299 := hb (x 16 7)
      have b26300 := hb (x 15 1 && x 15 8)
      have b26301 := hb (x 14 2 && x 14 9)
      have b26302 := hb (x 13 3 && x 13 10)
      have b26303 := hb (x 12 4 && x 12 11)
      have b26304 := hb (x 11 5 && x 11 12)
      have b26305 := hb (x 10 6 && x 10 13)
      have b26306 := hb (x 9 7 && x 9 14)
      clear * - r26297 b26298 b26299 b26300 b26301 b26302 b26303 b26304 b26305 b26306 d25388 d25412 d25436 d25460 d26029 d26045 d25766 d26272
      omega
    have d26307 : (x 23 8).toNat = 0 := by
      have r26308 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26309 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e26310 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e26311 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e26312 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e26313 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e26314 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have b26315 := hb (x 16 7)
      have b26316 := hb (x 17 6)
      have b26317 := hb (x 18 5)
      have b26318 := hb (x 19 4)
      have b26319 := hb (x 20 11)
      have b26320 := hb (x 21 10)
      have b26321 := hb (x 22 9)
      have b26322 := hb (x 23 8)
      clear * - r26308 e26309 e26310 e26311 e26312 e26313 e26314 b26315 b26316 b26317 b26318 b26319 b26320 b26321 b26322 d26296
      omega
    have d26323 : (x 22 9).toNat = 0 := by
      have r26324 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26325 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e26326 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e26327 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e26328 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e26329 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e26330 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have b26331 := hb (x 16 7)
      have b26332 := hb (x 17 6)
      have b26333 := hb (x 18 5)
      have b26334 := hb (x 19 4)
      have b26335 := hb (x 20 11)
      have b26336 := hb (x 21 10)
      have b26337 := hb (x 22 9)
      have b26338 := hb (x 23 8)
      clear * - r26324 e26325 e26326 e26327 e26328 e26329 e26330 b26331 b26332 b26333 b26334 b26335 b26336 b26337 b26338 d26307 d26296
      omega
    have d26339 : (x 21 10).toNat = 0 := by
      have r26340 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26341 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e26342 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e26343 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e26344 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e26345 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e26346 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have b26347 := hb (x 16 7)
      have b26348 := hb (x 17 6)
      have b26349 := hb (x 18 5)
      have b26350 := hb (x 19 4)
      have b26351 := hb (x 20 11)
      have b26352 := hb (x 21 10)
      have b26353 := hb (x 22 9)
      have b26354 := hb (x 23 8)
      clear * - r26340 e26341 e26342 e26343 e26344 e26345 e26346 b26347 b26348 b26349 b26350 b26351 b26352 b26353 b26354 d26307 d26323 d26296
      omega
    have d26355 : (x 20 11).toNat = 0 := by
      have r26356 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26357 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e26358 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e26359 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e26360 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e26361 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e26362 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have b26363 := hb (x 16 7)
      have b26364 := hb (x 17 6)
      have b26365 := hb (x 18 5)
      have b26366 := hb (x 19 4)
      have b26367 := hb (x 20 11)
      have b26368 := hb (x 21 10)
      have b26369 := hb (x 22 9)
      have b26370 := hb (x 23 8)
      clear * - r26356 e26357 e26358 e26359 e26360 e26361 e26362 b26363 b26364 b26365 b26366 b26367 b26368 b26369 b26370 d26307 d26323 d26339 d26296
      omega
    have d26371 : (x 19 4).toNat = 0 := by
      have r26372 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26373 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e26374 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e26375 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e26376 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e26377 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e26378 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have b26379 := hb (x 16 7)
      have b26380 := hb (x 17 6)
      have b26381 := hb (x 18 5)
      have b26382 := hb (x 19 4)
      have b26383 := hb (x 20 11)
      have b26384 := hb (x 21 10)
      have b26385 := hb (x 22 9)
      have b26386 := hb (x 23 8)
      clear * - r26372 e26373 e26374 e26375 e26376 e26377 e26378 b26379 b26380 b26381 b26382 b26383 b26384 b26385 b26386 d26307 d26323 d26339 d26355 d26296
      omega
    have d26387 : (x 18 5).toNat = 0 := by
      have r26388 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26389 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e26390 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e26391 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e26392 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e26393 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e26394 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have b26395 := hb (x 16 7)
      have b26396 := hb (x 17 6)
      have b26397 := hb (x 18 5)
      have b26398 := hb (x 19 4)
      have b26399 := hb (x 20 11)
      have b26400 := hb (x 21 10)
      have b26401 := hb (x 22 9)
      have b26402 := hb (x 23 8)
      clear * - r26388 e26389 e26390 e26391 e26392 e26393 e26394 b26395 b26396 b26397 b26398 b26399 b26400 b26401 b26402 d26307 d26323 d26339 d26355 d26371 d26296
      omega
    have d26403 : (x 17 6).toNat = 0 := by
      have r26404 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26405 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e26406 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e26407 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e26408 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e26409 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e26410 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have b26411 := hb (x 16 7)
      have b26412 := hb (x 17 6)
      have b26413 := hb (x 18 5)
      have b26414 := hb (x 19 4)
      have b26415 := hb (x 20 11)
      have b26416 := hb (x 21 10)
      have b26417 := hb (x 22 9)
      have b26418 := hb (x 23 8)
      clear * - r26404 e26405 e26406 e26407 e26408 e26409 e26410 b26411 b26412 b26413 b26414 b26415 b26416 b26417 b26418 d26307 d26323 d26339 d26355 d26371 d26387 d26296
      omega
    have d26419 : (x 17 1 && x 17 6).toNat = 0 := by
      have r26420 := hand2 (x 17 1) (x 17 6)
      have b26421 := hb (x 17 6)
      have b26422 := hb (x 17 1 && x 17 6)
      clear * - r26420 b26421 b26422 d26403
      omega
    have d26423 : (x 16 2 && x 16 7).toNat = 1 := by
      have r26424 : 1 ≤ (x 18 5).toNat + (x 17 1 && x 17 6).toNat + (x 16 2 && x 16 7).toNat + (x 15 3 && x 15 8).toNat + (x 14 4 && x 14 9).toNat + (x 13 5 && x 13 10).toNat + (x 12 6 && x 12 11).toNat + (x 11 7 && x 11 12).toNat + (x 10 8 && x 10 13).toNat + (x 9 9 && x 9 14).toNat + (x 8 10).toNat := by have q := hcov5 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26425 := hb (x 8 10)
      have b26426 := hb (x 18 5)
      have b26427 := hb (x 17 1 && x 17 6)
      have b26428 := hb (x 16 2 && x 16 7)
      have b26429 := hb (x 15 3 && x 15 8)
      have b26430 := hb (x 14 4 && x 14 9)
      have b26431 := hb (x 13 5 && x 13 10)
      have b26432 := hb (x 12 6 && x 12 11)
      have b26433 := hb (x 11 7 && x 11 12)
      have b26434 := hb (x 10 8 && x 10 13)
      have b26435 := hb (x 9 9 && x 9 14)
      clear * - r26424 b26425 b26426 b26427 b26428 b26429 b26430 b26431 b26432 b26433 b26434 b26435 d26387 d26419 d25392 d25416 d25440 d25464 d26033 d26049 d25770 d26236
      omega
    have d26436 : (x 16 2).toNat = 1 := by
      have r26437 := hand1 (x 16 2) (x 16 7)
      have b26438 := hb (x 16 2)
      have b26439 := hb (x 16 2 && x 16 7)
      clear * - r26437 b26438 b26439 d26423
      omega
    have d26440 : (x 16 14).toNat = 1 := by
      have r26441 : (x 16 2).toNat ≤ (x 16 14).toNat := himp _ _ (hp2 16)
      have b26442 := hb (x 16 2)
      have b26443 := hb (x 16 14)
      clear * - r26441 b26442 b26443 d26436
      omega
    have d26444 : (x 15 1).toNat = 0 := by
      have r26445 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26446 := hb (x 15 1)
      have b26447 := hb (x 16 14)
      clear * - r26445 b26446 b26447 d26440
      omega
    have d26448 : (x 15 1 && x 15 11).toNat = 0 := by
      have r26449 := hand1 (x 15 1) (x 15 11)
      have b26450 := hb (x 15 1)
      have b26451 := hb (x 15 1 && x 15 11)
      clear * - r26449 b26450 b26451 d26444
      omega
    have d26452 : (x 15 1 && x 15 7).toNat = 0 := by
      have r26453 := hand1 (x 15 1) (x 15 7)
      have b26454 := hb (x 15 1)
      have b26455 := hb (x 15 1 && x 15 7)
      clear * - r26453 b26454 b26455 d26444
      omega
    have d26456 : (x 16 6).toNat = 1 := by
      have r26457 : 1 ≤ (x 16 6).toNat + (x 15 1 && x 15 7).toNat + (x 14 2 && x 14 8).toNat + (x 13 3 && x 13 9).toNat + (x 12 4 && x 12 10).toNat + (x 11 5 && x 11 11).toNat + (x 10 6 && x 10 12).toNat + (x 9 7 && x 9 13).toNat + (x 8 8 && x 8 14).toNat + (x 7 9).toNat := by have q := hcov6 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26458 := hb (x 7 9)
      have b26459 := hb (x 16 6)
      have b26460 := hb (x 15 1 && x 15 7)
      have b26461 := hb (x 14 2 && x 14 8)
      have b26462 := hb (x 13 3 && x 13 9)
      have b26463 := hb (x 12 4 && x 12 10)
      have b26464 := hb (x 11 5 && x 11 11)
      have b26465 := hb (x 10 6 && x 10 12)
      have b26466 := hb (x 9 7 && x 9 13)
      have b26467 := hb (x 8 8 && x 8 14)
      clear * - r26457 b26458 b26459 b26460 b26461 b26462 b26463 b26464 b26465 b26466 b26467 d26452 d25597 d25617 d25637 d25661 d25697 d26065 d26288 d25677
      omega
    have d26468 : (x 22 8).toNat = 0 := by
      have r26469 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26470 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
      have e26471 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
      have e26472 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
      have e26473 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
      have e26474 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
      have e26475 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
      have b26476 := hb (x 15 7)
      have b26477 := hb (x 16 6)
      have b26478 := hb (x 17 5)
      have b26479 := hb (x 18 4)
      have b26480 := hb (x 19 11)
      have b26481 := hb (x 20 10)
      have b26482 := hb (x 21 9)
      have b26483 := hb (x 22 8)
      clear * - r26469 e26470 e26471 e26472 e26473 e26474 e26475 b26476 b26477 b26478 b26479 b26480 b26481 b26482 b26483 d26456
      omega
    have d26484 : (x 21 9).toNat = 0 := by
      have r26485 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26486 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
      have e26487 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
      have e26488 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
      have e26489 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
      have e26490 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
      have e26491 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
      have b26492 := hb (x 15 7)
      have b26493 := hb (x 16 6)
      have b26494 := hb (x 17 5)
      have b26495 := hb (x 18 4)
      have b26496 := hb (x 19 11)
      have b26497 := hb (x 20 10)
      have b26498 := hb (x 21 9)
      have b26499 := hb (x 22 8)
      clear * - r26485 e26486 e26487 e26488 e26489 e26490 e26491 b26492 b26493 b26494 b26495 b26496 b26497 b26498 b26499 d26468 d26456
      omega
    have d26500 : (x 20 10).toNat = 0 := by
      have r26501 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26502 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
      have e26503 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
      have e26504 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
      have e26505 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
      have e26506 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
      have e26507 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
      have b26508 := hb (x 15 7)
      have b26509 := hb (x 16 6)
      have b26510 := hb (x 17 5)
      have b26511 := hb (x 18 4)
      have b26512 := hb (x 19 11)
      have b26513 := hb (x 20 10)
      have b26514 := hb (x 21 9)
      have b26515 := hb (x 22 8)
      clear * - r26501 e26502 e26503 e26504 e26505 e26506 e26507 b26508 b26509 b26510 b26511 b26512 b26513 b26514 b26515 d26468 d26484 d26456
      omega
    have d26516 : (x 19 11).toNat = 0 := by
      have r26517 : (x 22 8).toNat + (x 21 1 && x 21 9).toNat + (x 20 2 && x 20 10).toNat + (x 19 3 && x 19 11).toNat + (x 18 4 && x 18 12).toNat + (x 17 5 && x 17 13).toNat + (x 16 6 && x 16 14).toNat + (x 15 7).toNat = 1 := by have q := hd8 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26518 : (x 21 1 && x 21 9).toNat = (x 21 9).toNat := handr _ _ (fun h => hp9 21 (h))
      have e26519 : (x 20 2 && x 20 10).toNat = (x 20 10).toNat := handr _ _ (fun h => hp10 20 (h))
      have e26520 : (x 19 3 && x 19 11).toNat = (x 19 11).toNat := handr _ _ (fun h => hp11 19 (h))
      have e26521 : (x 18 4 && x 18 12).toNat = (x 18 4).toNat := handl _ _ (fun h => hp4 18 (h))
      have e26522 : (x 17 5 && x 17 13).toNat = (x 17 5).toNat := handl _ _ (fun h => hp5 17 (h))
      have e26523 : (x 16 6 && x 16 14).toNat = (x 16 6).toNat := handl _ _ (fun h => hp6 16 (h))
      have b26524 := hb (x 15 7)
      have b26525 := hb (x 16 6)
      have b26526 := hb (x 17 5)
      have b26527 := hb (x 18 4)
      have b26528 := hb (x 19 11)
      have b26529 := hb (x 20 10)
      have b26530 := hb (x 21 9)
      have b26531 := hb (x 22 8)
      clear * - r26517 e26518 e26519 e26520 e26521 e26522 e26523 b26524 b26525 b26526 b26527 b26528 b26529 b26530 b26531 d26468 d26484 d26500 d26456
      omega
    have d26532 : (x 19 1 && x 19 11).toNat = 0 := by
      have r26533 := hand2 (x 19 1) (x 19 11)
      have b26534 := hb (x 19 11)
      have b26535 := hb (x 19 1 && x 19 11)
      clear * - r26533 b26534 b26535 d26516
      omega
    have d26536 : (x 15 13).toNat = 0 := by
      have r26537 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
      have b26538 := hb (x 15 1)
      have b26539 := hb (x 15 13)
      clear * - r26537 b26538 b26539 d26444
      omega
    have d26540 : (x 15 5).toNat = 0 := by
      have r26541 : (x 15 5).toNat ≤ (x 15 13).toNat := himp _ _ (hp5 15)
      have b26542 := hb (x 15 5)
      have b26543 := hb (x 15 13)
      clear * - r26541 b26542 b26543 d26536
      omega
    have d26544 : (x 18 12).toNat = 0 := by
      have r26545 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26546 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e26547 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b26548 := hb (x 15 3)
      have b26549 := hb (x 16 2)
      have b26550 := hb (x 17 13)
      have b26551 := hb (x 18 12)
      clear * - r26545 e26546 e26547 b26548 b26549 b26550 b26551 d26436
      omega
    have d26552 : (x 18 2 && x 18 12).toNat = 0 := by
      have r26553 := hand2 (x 18 2) (x 18 12)
      have b26554 := hb (x 18 12)
      have b26555 := hb (x 18 2 && x 18 12)
      clear * - r26553 b26554 b26555 d26544
      omega
    have d26556 : (x 17 13).toNat = 0 := by
      have r26557 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26558 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e26559 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b26560 := hb (x 15 3)
      have b26561 := hb (x 16 2)
      have b26562 := hb (x 17 13)
      have b26563 := hb (x 18 12)
      clear * - r26557 e26558 e26559 b26560 b26561 b26562 b26563 d26544 d26436
      omega
    have d26564 : (x 17 3 && x 17 13).toNat = 0 := by
      have r26565 := hand2 (x 17 3) (x 17 13)
      have b26566 := hb (x 17 13)
      have b26567 := hb (x 17 3 && x 17 13)
      clear * - r26565 b26566 b26567 d26556
      omega
    have d26568 : (x 16 4 && x 16 14).toNat = 1 := by
      have r26569 : 1 ≤ (x 20 10).toNat + (x 19 1 && x 19 11).toNat + (x 18 2 && x 18 12).toNat + (x 17 3 && x 17 13).toNat + (x 16 4 && x 16 14).toNat + (x 15 5).toNat := by have q := hcov10 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26570 := hb (x 15 5)
      have b26571 := hb (x 20 10)
      have b26572 := hb (x 19 1 && x 19 11)
      have b26573 := hb (x 18 2 && x 18 12)
      have b26574 := hb (x 17 3 && x 17 13)
      have b26575 := hb (x 16 4 && x 16 14)
      clear * - r26569 b26570 b26571 b26572 b26573 b26574 b26575 d26500 d26532 d26552 d26564 d26540
      omega
    have d26576 : (x 16 4).toNat = 1 := by
      have r26577 := hand1 (x 16 4) (x 16 14)
      have b26578 := hb (x 16 4)
      have b26579 := hb (x 16 4 && x 16 14)
      clear * - r26577 b26578 b26579 d26568
      omega
    have d26580 : (x 16 12).toNat = 1 := by
      have r26581 : (x 16 4).toNat ≤ (x 16 12).toNat := himp _ _ (hp4 16)
      have b26582 := hb (x 16 4)
      have b26583 := hb (x 16 12)
      clear * - r26581 b26582 b26583 d26576
      omega
    have d26584 : (x 14 2).toNat = 0 := by
      have r26585 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26586 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e26587 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b26588 := hb (x 13 3)
      have b26589 := hb (x 14 2)
      have b26590 := hb (x 15 13)
      have b26591 := hb (x 16 12)
      clear * - r26585 e26586 e26587 b26588 b26589 b26590 b26591 d26580 d26536
      omega
    have d26592 : (x 14 2 && x 14 12).toNat = 0 := by
      have r26593 := hand1 (x 14 2) (x 14 12)
      have b26594 := hb (x 14 2)
      have b26595 := hb (x 14 2 && x 14 12)
      clear * - r26593 b26594 b26595 d26584
      omega
    have d26596 : (x 14 1 && x 14 2).toNat = 0 := by
      have r26597 := hand2 (x 14 1) (x 14 2)
      have b26598 := hb (x 14 2)
      have b26599 := hb (x 14 1 && x 14 2)
      clear * - r26597 b26598 b26599 d26584
      omega
    have d26600 : (x 13 3).toNat = 0 := by
      have r26601 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26602 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e26603 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b26604 := hb (x 13 3)
      have b26605 := hb (x 14 2)
      have b26606 := hb (x 15 13)
      have b26607 := hb (x 16 12)
      clear * - r26601 e26602 e26603 b26604 b26605 b26606 b26607 d26580 d26536 d26584
      omega
    have d26608 : (x 13 3 && x 13 13).toNat = 0 := by
      have r26609 := hand1 (x 13 3) (x 13 13)
      have b26610 := hb (x 13 3)
      have b26611 := hb (x 13 3 && x 13 13)
      clear * - r26609 b26610 b26611 d26600
      omega
    have d26612 : (x 13 2 && x 13 3).toNat = 0 := by
      have r26613 := hand2 (x 13 2) (x 13 3)
      have b26614 := hb (x 13 3)
      have b26615 := hb (x 13 2 && x 13 3)
      clear * - r26613 b26614 b26615 d26600
      omega
    have d26616 : (x 12 3 && x 12 4).toNat = 1 := by
      have r26617 : 1 ≤ (x 15 1).toNat + (x 14 1 && x 14 2).toNat + (x 13 2 && x 13 3).toNat + (x 12 3 && x 12 4).toNat + (x 11 4 && x 11 5).toNat + (x 10 5 && x 10 6).toNat + (x 9 6 && x 9 7).toNat + (x 8 7 && x 8 8).toNat + (x 7 8 && x 7 9).toNat + (x 6 9 && x 6 10).toNat + (x 5 10 && x 5 11).toNat + (x 4 11 && x 4 12).toNat + (x 3 12 && x 3 13).toNat + (x 2 13 && x 2 14).toNat + (x 1 14).toNat := by have q := hcov1 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26618 := hb (x 1 14)
      have b26619 := hb (x 15 1)
      have b26620 := hb (x 14 1 && x 14 2)
      have b26621 := hb (x 13 2 && x 13 3)
      have b26622 := hb (x 12 3 && x 12 4)
      have b26623 := hb (x 11 4 && x 11 5)
      have b26624 := hb (x 10 5 && x 10 6)
      have b26625 := hb (x 9 6 && x 9 7)
      have b26626 := hb (x 8 7 && x 8 8)
      have b26627 := hb (x 7 8 && x 7 9)
      have b26628 := hb (x 6 9 && x 6 10)
      have b26629 := hb (x 5 10 && x 5 11)
      have b26630 := hb (x 4 11 && x 4 12)
      have b26631 := hb (x 3 12 && x 3 13)
      have b26632 := hb (x 2 13 && x 2 14)
      clear * - r26617 b26618 b26619 b26620 b26621 b26622 b26623 b26624 b26625 b26626 b26627 b26628 b26629 b26630 b26631 b26632 d26444 d26596 d26612 d25484 d25504 d25528 d26292 d25267 d25295 d25323 d25351 g16 g17 g10
      omega
    have d26633 : (x 12 4).toNat = 1 := by
      have r26634 := hand2 (x 12 3) (x 12 4)
      have b26635 := hb (x 12 4)
      have b26636 := hb (x 12 3 && x 12 4)
      clear * - r26634 b26635 b26636 d26616
      omega
    have d26637 : (x 12 12).toNat = 1 := by
      have r26638 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
      have b26639 := hb (x 12 4)
      have b26640 := hb (x 12 12)
      clear * - r26638 b26639 b26640 d26633
      omega
    have d26641 : (x 11 13).toNat = 0 := by
      have r26642 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26643 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e26644 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b26645 := hb (x 9 3)
      have b26646 := hb (x 10 2)
      have b26647 := hb (x 11 13)
      have b26648 := hb (x 12 12)
      clear * - r26642 e26643 e26644 b26645 b26646 b26647 b26648 d26637
      omega
    have d26649 : (x 11 5).toNat = 0 := by
      have r26650 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
      have b26651 := hb (x 11 5)
      have b26652 := hb (x 11 13)
      clear * - r26650 b26651 b26652 d26641
      omega
    have d26653 : (x 10 1 && x 10 14).toNat = 1 := by
      have r26654 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26655 := hb (x 9 2)
      have b26656 := hb (x 11 13)
      have b26657 := hb (x 10 1 && x 10 14)
      clear * - r26654 b26655 b26656 b26657 d26641 d25774
      omega
    have d26658 : (x 10 1).toNat = 1 := by
      have r26659 := hand1 (x 10 1) (x 10 14)
      have b26660 := hb (x 10 1)
      have b26661 := hb (x 10 1 && x 10 14)
      clear * - r26659 b26660 b26661 d26653
      omega
    have d26662 : (x 4 7).toNat = 0 := by
      have r26663 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26664 := hb (x (-3) 14)
      have b26665 := hb (x (-2) 13)
      have b26666 := hb (x (-1) 12)
      have b26667 := hb (x 0 11)
      have b26668 := hb (x 1 10)
      have b26669 := hb (x 2 9)
      have b26670 := hb (x 3 8)
      have b26671 := hb (x 4 7)
      have b26672 := hb (x 5 6)
      have b26673 := hb (x 6 5)
      have b26674 := hb (x 7 4)
      have b26675 := hb (x 8 3)
      have b26676 := hb (x 9 2)
      have b26677 := hb (x 10 1)
      clear * - r26663 b26664 b26665 b26666 b26667 b26668 b26669 b26670 b26671 b26672 b26673 b26674 b26675 b26676 b26677 d26658 d25774 d26017 d26002 d26061 d25961 g14 g12 g9 g5
      omega
    have d26678 : (x 4 7 && x 4 14).toNat = 0 := by
      have r26679 := hand1 (x 4 7) (x 4 14)
      have b26680 := hb (x 4 7)
      have b26681 := hb (x 4 7 && x 4 14)
      clear * - r26679 b26680 b26681 d26662
      omega
    have d26682 : (x 11 7).toNat = 1 := by
      have r26683 : 1 ≤ (x 11 7).toNat + (x 10 1 && x 10 8).toNat + (x 9 2 && x 9 9).toNat + (x 8 3 && x 8 10).toNat + (x 7 4 && x 7 11).toNat + (x 6 5 && x 6 12).toNat + (x 5 6 && x 5 13).toNat + (x 4 7 && x 4 14).toNat + (x 3 8).toNat := by have q := hcov7 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26684 := hb (x 3 8)
      have b26685 := hb (x 11 7)
      have b26686 := hb (x 10 1 && x 10 8)
      have b26687 := hb (x 9 2 && x 9 9)
      have b26688 := hb (x 8 3 && x 8 10)
      have b26689 := hb (x 7 4 && x 7 11)
      have b26690 := hb (x 6 5 && x 6 12)
      have b26691 := hb (x 5 6 && x 5 13)
      have b26692 := hb (x 4 7 && x 4 14)
      clear * - r26683 b26684 b26685 b26686 b26687 b26688 b26689 b26690 b26691 b26692 d26208 d25778 d26252 d26006 d25887 d25911 d26678 g14
      omega
    have d26693 : (x 18 8).toNat = 0 := by
      have r26694 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26695 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e26696 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e26697 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e26698 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e26699 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e26700 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b26701 := hb (x 11 7)
      have b26702 := hb (x 12 6)
      have b26703 := hb (x 13 5)
      have b26704 := hb (x 14 4)
      have b26705 := hb (x 15 11)
      have b26706 := hb (x 16 10)
      have b26707 := hb (x 17 9)
      have b26708 := hb (x 18 8)
      clear * - r26694 e26695 e26696 e26697 e26698 e26699 e26700 b26701 b26702 b26703 b26704 b26705 b26706 b26707 b26708 d26682
      omega
    have d26709 : (x 17 9).toNat = 0 := by
      have r26710 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26711 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e26712 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e26713 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e26714 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e26715 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e26716 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b26717 := hb (x 11 7)
      have b26718 := hb (x 12 6)
      have b26719 := hb (x 13 5)
      have b26720 := hb (x 14 4)
      have b26721 := hb (x 15 11)
      have b26722 := hb (x 16 10)
      have b26723 := hb (x 17 9)
      have b26724 := hb (x 18 8)
      clear * - r26710 e26711 e26712 e26713 e26714 e26715 e26716 b26717 b26718 b26719 b26720 b26721 b26722 b26723 b26724 d26693 d26682
      omega
    have d26725 : (x 16 10).toNat = 0 := by
      have r26726 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26727 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
      have e26728 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
      have e26729 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
      have e26730 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
      have e26731 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
      have e26732 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
      have b26733 := hb (x 11 7)
      have b26734 := hb (x 12 6)
      have b26735 := hb (x 13 5)
      have b26736 := hb (x 14 4)
      have b26737 := hb (x 15 11)
      have b26738 := hb (x 16 10)
      have b26739 := hb (x 17 9)
      have b26740 := hb (x 18 8)
      clear * - r26726 e26727 e26728 e26729 e26730 e26731 e26732 b26733 b26734 b26735 b26736 b26737 b26738 b26739 b26740 d26693 d26709 d26682
      omega
    have d26741 : (x 12 4 && x 12 14).toNat = 1 := by
      have r26742 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := by have q := hcov10 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26743 := hb (x 11 5)
      have b26744 := hb (x 16 10)
      have b26745 := hb (x 15 1 && x 15 11)
      have b26746 := hb (x 14 2 && x 14 12)
      have b26747 := hb (x 13 3 && x 13 13)
      have b26748 := hb (x 12 4 && x 12 14)
      clear * - r26742 b26743 b26744 b26745 b26746 b26747 b26748 d26725 d26448 d26592 d26608 d26649
      omega
    have d26749 : (x 12 14).toNat = 1 := by
      have r26750 := hand2 (x 12 4) (x 12 14)
      have b26751 := hb (x 12 14)
      have b26752 := hb (x 12 4 && x 12 14)
      clear * - r26750 b26751 b26752 d26741
      omega
    have d26753 : (x 11 1).toNat = 0 := by
      have r26754 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26755 := hb (x 11 1)
      have b26756 := hb (x 12 14)
      clear * - r26754 b26755 b26756 d26749
      omega
    have d26757 : (x 11 1 && x 11 7).toNat = 0 := by
      have r26758 := hand1 (x 11 1) (x 11 7)
      have b26759 := hb (x 11 1)
      have b26760 := hb (x 11 1 && x 11 7)
      clear * - r26758 b26759 b26760 d26753
      omega
    have d26761 : (x 12 6).toNat = 1 := by
      have r26762 : 1 ≤ (x 12 6).toNat + (x 11 1 && x 11 7).toNat + (x 10 2 && x 10 8).toNat + (x 9 3 && x 9 9).toNat + (x 8 4 && x 8 10).toNat + (x 7 5 && x 7 11).toNat + (x 6 6 && x 6 12).toNat + (x 5 7 && x 5 13).toNat + (x 4 8 && x 4 14).toNat + (x 3 9).toNat := by have q := hcov6 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26763 := hb (x 3 9)
      have b26764 := hb (x 12 6)
      have b26765 := hb (x 11 1 && x 11 7)
      have b26766 := hb (x 10 2 && x 10 8)
      have b26767 := hb (x 9 3 && x 9 9)
      have b26768 := hb (x 8 4 && x 8 10)
      have b26769 := hb (x 7 5 && x 7 11)
      have b26770 := hb (x 6 6 && x 6 12)
      have b26771 := hb (x 5 7 && x 5 13)
      have b26772 := hb (x 4 8 && x 4 14)
      clear * - r26762 b26763 b26764 b26765 b26766 b26767 b26768 b26769 b26770 b26771 b26772 d26757 d26212 d26232 d26256 d25673 d25891 d25915 g32 g15
      omega
    have r26773 : (x 18 8).toNat + (x 17 1 && x 17 9).toNat + (x 16 2 && x 16 10).toNat + (x 15 3 && x 15 11).toNat + (x 14 4 && x 14 12).toNat + (x 13 5 && x 13 13).toNat + (x 12 6 && x 12 14).toNat + (x 11 7).toNat = 1 := by have q := hd8 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26774 : (x 17 1 && x 17 9).toNat = (x 17 9).toNat := handr _ _ (fun h => hp9 17 (h))
    have e26775 : (x 16 2 && x 16 10).toNat = (x 16 10).toNat := handr _ _ (fun h => hp10 16 (h))
    have e26776 : (x 15 3 && x 15 11).toNat = (x 15 11).toNat := handr _ _ (fun h => hp11 15 (h))
    have e26777 : (x 14 4 && x 14 12).toNat = (x 14 4).toNat := handl _ _ (fun h => hp4 14 (h))
    have e26778 : (x 13 5 && x 13 13).toNat = (x 13 5).toNat := handl _ _ (fun h => hp5 13 (h))
    have e26779 : (x 12 6 && x 12 14).toNat = (x 12 6).toNat := handl _ _ (fun h => hp6 12 (h))
    have b26780 := hb (x 11 7)
    have b26781 := hb (x 12 6)
    have b26782 := hb (x 13 5)
    have b26783 := hb (x 14 4)
    have b26784 := hb (x 15 11)
    have b26785 := hb (x 16 10)
    have b26786 := hb (x 17 9)
    have b26787 := hb (x 18 8)
    linarith only [r26773, e26774, e26775, e26776, e26777, e26778, e26779, b26780, b26781, b26782, b26783, b26784, b26785, b26786, b26787, d26693, d26709, d26725, d26761, d26682]
  · have f26788 : (x 0 8).toNat = 1 := by rw [h25355]; rfl
    have d26789 : (x (-4) 4).toNat = 0 := by
      have r26790 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e26791 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
      have e26792 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
      have e26793 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
      have e26794 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
      have e26795 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
      have e26796 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
      have b26797 := hb (x (-7) 7)
      have b26798 := hb (x (-6) 6)
      have b26799 := hb (x (-5) 5)
      have b26800 := hb (x (-4) 4)
      have b26801 := hb (x (-3) 11)
      have b26802 := hb (x (-2) 10)
      have b26803 := hb (x (-1) 9)
      have b26804 := hb (x 0 8)
      clear * - r26790 e26791 e26792 e26793 e26794 e26795 e26796 b26797 b26798 b26799 b26800 b26801 b26802 b26803 b26804 f26788 g2 g1 g0
      omega
    have d26805 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
      have r26806 := hand1 (x (-4) 4) (x (-4) 14)
      have b26807 := hb (x (-4) 4)
      have b26808 := hb (x (-4) 4 && x (-4) 14)
      clear * - r26806 b26807 b26808 d26789
      omega
    have d26809 : (x (-5) 5).toNat = 1 := by
      have r26810 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b26811 := hb (x (-5) 5)
      have b26812 := hb (x 0 10)
      have b26813 := hb (x (-1) 1 && x (-1) 11)
      have b26814 := hb (x (-2) 2 && x (-2) 12)
      have b26815 := hb (x (-3) 3 && x (-3) 13)
      have b26816 := hb (x (-4) 4 && x (-4) 14)
      clear * - r26810 b26811 b26812 b26813 b26814 b26815 b26816 g4 g38 g39 g40 d26805
      omega
    have r26817 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e26818 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e26819 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e26820 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e26821 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e26822 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e26823 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have b26824 := hb (x (-7) 7)
    have b26825 := hb (x (-6) 6)
    have b26826 := hb (x (-5) 5)
    have b26827 := hb (x (-4) 4)
    have b26828 := hb (x (-3) 11)
    have b26829 := hb (x (-2) 10)
    have b26830 := hb (x (-1) 9)
    have b26831 := hb (x 0 8)
    linarith only [r26817, e26818, e26819, e26820, e26821, e26822, e26823, b26824, b26825, b26826, b26827, b26828, b26829, b26830, b26831, f26788, g2, g1, g0, d26789, d26809]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_a0_aux (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-3) 5).toNat = 0)
    (g2 : (x (-2) 4).toNat = 0)
    (g3 : (x (-1) 5).toNat = 0)
    (g4 : (x (-1) 9).toNat = 0)
    (g5 : (x (-1) 13).toNat = 0)
    (g6 : (x 0 4).toNat = 0)
    (g7 : (x 0 11).toNat = 0)
    (g8 : (x 0 14).toNat = 1)
    (g9 : (x 1 5).toNat = 0)
    (g10 : (x 1 9).toNat = 0)
    (g11 : (x 1 13).toNat = 0)
    (g12 : (x 2 4).toNat = 0)
    (g13 : (x 2 12).toNat = 0)
    (g14 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g15 : (x (-2) 4 && x (-2) 8).toNat = 0)
    (g16 : (x (-3) 5 && x (-3) 9).toNat = 0)
    (g17 : (x (-4) 6 && x (-4) 10).toNat = 0)
    (g18 : (x (-5) 7 && x (-5) 11).toNat = 0)
    (g19 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g20 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g21 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g22 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g23 : (x (-4) 6 && x (-4) 12).toNat = 0)
    (g24 : (x (-5) 7 && x (-5) 13).toNat = 0)
    (g25 : (x 2 6 && x 2 12).toNat = 0)
    (g26 : (x 1 7 && x 1 13).toNat = 0)
    (g27 : (x 2 8 && x 2 14).toNat = 0)
    (g28 : (x 0 2 && x 0 11).toNat = 0)
    (g29 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g30 : (x (-2) 4 && x (-2) 13).toNat = 0)
    (g31 : (x (-3) 5 && x (-3) 14).toNat = 0)
    (g32 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g33 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g34 : (x 2 4 && x 2 13).toNat = 0)
    (g35 : (x 1 5 && x 1 14).toNat = 0)
    (g36 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g37 : (x (-2) 4 && x (-2) 14).toNat = 0)
    (g38 : (x 2 2 && x 2 12).toNat = 0)
    (g39 : (x 1 3 && x 1 13).toNat = 0)
    (g40 : (x 2 4 && x 2 14).toNat = 0)
    (g41 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g42 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g43 : (x (-1) 3 && x (-1) 14).toNat = 0)
    (g44 : (x 2 1 && x 2 12).toNat = 0)
    (g45 : (x 1 2 && x 1 13).toNat = 0)
    (g46 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d27178 : (x 0 4 && x 0 14).toNat = 0 := by
    have r27179 := hand1 (x 0 4) (x 0 14)
    have b27180 := hb (x 0 4)
    have b27181 := hb (x 0 4 && x 0 14)
    clear * - r27179 b27180 b27181 g6
    omega
  have d27182 : (x 0 4 && x 0 13).toNat = 0 := by
    have r27183 := hand1 (x 0 4) (x 0 13)
    have b27184 := hb (x 0 4)
    have b27185 := hb (x 0 4 && x 0 13)
    clear * - r27183 b27184 b27185 g6
    omega
  cases h27186 : x 0 1
  · have f27187 : (x 0 1).toNat = 0 := by rw [h27186]; rfl
    have d27188 : (x 0 1 && x 0 14).toNat = 0 := by
      have r27189 := hand1 (x 0 1) (x 0 14)
      have b27190 := hb (x 0 1)
      have b27191 := hb (x 0 1 && x 0 14)
      clear * - r27189 b27190 b27191 f27187
      omega
    have d27192 : (x 0 1 && x 0 12).toNat = 0 := by
      have r27193 := hand1 (x 0 1) (x 0 12)
      have b27194 := hb (x 0 1)
      have b27195 := hb (x 0 1 && x 0 12)
      clear * - r27193 b27194 b27195 f27187
      omega
    have d27196 : (x 0 13).toNat = 0 := by
      have r27197 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
      have b27198 := hb (x 0 1)
      have b27199 := hb (x 0 13)
      clear * - r27197 b27198 b27199 f27187
      omega
    have d27200 : (x 0 2 && x 0 13).toNat = 0 := by
      have r27201 := hand2 (x 0 2) (x 0 13)
      have b27202 := hb (x 0 13)
      have b27203 := hb (x 0 2 && x 0 13)
      clear * - r27201 b27202 b27203 d27196
      omega
    have d27204 : (x (-1) 2).toNat = 1 := by
      have r27205 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27206 := hb (x (-1) 2)
      have b27207 := hb (x 1 13)
      have b27208 := hb (x 0 1 && x 0 14)
      clear * - r27205 b27206 b27207 b27208 g11 d27188
      omega
    have d27209 : (x (-1) 14).toNat = 1 := by
      have r27210 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
      have b27211 := hb (x (-1) 2)
      have b27212 := hb (x (-1) 14)
      clear * - r27210 b27211 b27212 d27204
      omega
    have d27213 : (x (-2) 1).toNat = 0 := by
      have r27214 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := by have q := hd14 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27215 := hb (x (-2) 1)
      have b27216 := hb (x (-1) 14)
      clear * - r27214 b27215 b27216 d27209
      omega
    have d27217 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
      have r27218 := hand1 (x (-2) 1) (x (-2) 14)
      have b27219 := hb (x (-2) 1)
      have b27220 := hb (x (-2) 1 && x (-2) 14)
      clear * - r27218 b27219 b27220 d27213
      omega
    have d27221 : (x (-2) 13).toNat = 0 := by
      have r27222 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
      have b27223 := hb (x (-2) 1)
      have b27224 := hb (x (-2) 13)
      clear * - r27222 b27223 b27224 d27213
      omega
    have d27225 : (x (-2) 2).toNat = 1 := by
      have r27226 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27227 := hb (x (-2) 2)
      have b27228 := hb (x 0 13)
      have b27229 := hb (x (-1) 1 && x (-1) 14)
      clear * - r27226 b27227 b27228 b27229 d27196 g46
      omega
    have d27230 : (x (-2) 14).toNat = 1 := by
      have r27231 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
      have b27232 := hb (x (-2) 2)
      have b27233 := hb (x (-2) 14)
      clear * - r27231 b27232 b27233 d27225
      omega
    have d27234 : (x (-3) 1).toNat = 0 := by
      have r27235 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27236 := hb (x (-3) 1)
      have b27237 := hb (x (-2) 14)
      clear * - r27235 b27236 b27237 d27230
      omega
    have d27238 : (x (-3) 13).toNat = 0 := by
      have r27239 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
      have b27240 := hb (x (-3) 1)
      have b27241 := hb (x (-3) 13)
      clear * - r27239 b27240 b27241 d27234
      omega
    have d27242 : (x (-3) 2).toNat = 1 := by
      have r27243 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27244 := hb (x (-3) 2)
      have b27245 := hb (x (-1) 13)
      have b27246 := hb (x (-2) 1 && x (-2) 14)
      clear * - r27243 b27244 b27245 b27246 g5 d27217
      omega
    have d27247 : (x (-3) 14).toNat = 1 := by
      have r27248 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
      have b27249 := hb (x (-3) 2)
      have b27250 := hb (x (-3) 14)
      clear * - r27248 b27249 b27250 d27242
      omega
    have d27251 : (x (-4) 1).toNat = 0 := by
      have r27252 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27253 := hb (x (-4) 1)
      have b27254 := hb (x (-3) 14)
      clear * - r27252 b27253 b27254 d27247
      omega
    have d27255 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
      have r27256 := hand1 (x (-4) 1) (x (-4) 14)
      have b27257 := hb (x (-4) 1)
      have b27258 := hb (x (-4) 1 && x (-4) 14)
      clear * - r27256 b27257 b27258 d27251
      omega
    have d27259 : (x (-4) 13).toNat = 0 := by
      have r27260 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
      have b27261 := hb (x (-4) 1)
      have b27262 := hb (x (-4) 13)
      clear * - r27260 b27261 b27262 d27251
      omega
    have d27263 : (x (-5) 2).toNat = 1 := by
      have r27264 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27265 := hb (x (-5) 2)
      have b27266 := hb (x (-3) 13)
      have b27267 := hb (x (-4) 1 && x (-4) 14)
      clear * - r27264 b27265 b27266 b27267 d27238 d27255
      omega
    have d27268 : (x 1 12).toNat = 0 := by
      have r27269 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27270 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e27271 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b27272 := hb (x (-2) 3)
      have b27273 := hb (x (-1) 2)
      have b27274 := hb (x 0 13)
      have b27275 := hb (x 1 12)
      clear * - r27269 e27270 e27271 b27272 b27273 b27274 b27275 d27196 d27204
      omega
    have d27276 : (x 1 1 && x 1 12).toNat = 0 := by
      have r27277 := hand2 (x 1 1) (x 1 12)
      have b27278 := hb (x 1 12)
      have b27279 := hb (x 1 1 && x 1 12)
      clear * - r27277 b27278 b27279 d27268
      omega
    have d27280 : (x (-2) 3).toNat = 0 := by
      have r27281 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27282 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e27283 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b27284 := hb (x (-2) 3)
      have b27285 := hb (x (-1) 2)
      have b27286 := hb (x 0 13)
      have b27287 := hb (x 1 12)
      clear * - r27281 e27282 e27283 b27284 b27285 b27286 b27287 d27268 d27196 d27204
      omega
    have d27288 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
      have r27289 := hand1 (x (-2) 3) (x (-2) 14)
      have b27290 := hb (x (-2) 3)
      have b27291 := hb (x (-2) 3 && x (-2) 14)
      clear * - r27289 b27290 b27291 d27280
      omega
    have d27292 : (x (-1) 12).toNat = 0 := by
      have r27293 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27294 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e27295 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b27296 := hb (x (-4) 3)
      have b27297 := hb (x (-3) 2)
      have b27298 := hb (x (-2) 13)
      have b27299 := hb (x (-1) 12)
      clear * - r27293 e27294 e27295 b27296 b27297 b27298 b27299 d27221 d27242
      omega
    have d27300 : (x (-1) 4).toNat = 0 := by
      have r27301 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
      have b27302 := hb (x (-1) 4)
      have b27303 := hb (x (-1) 12)
      clear * - r27301 b27302 b27303 d27292
      omega
    have d27304 : (x (-3) 12).toNat = 0 := by
      have r27305 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27306 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
      have e27307 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
      have b27308 := hb (x (-6) 3)
      have b27309 := hb (x (-5) 2)
      have b27310 := hb (x (-4) 13)
      have b27311 := hb (x (-3) 12)
      clear * - r27305 e27306 e27307 b27308 b27309 b27310 b27311 d27259 d27263
      omega
    have d27312 : (x (-3) 4).toNat = 0 := by
      have r27313 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
      have b27314 := hb (x (-3) 4)
      have b27315 := hb (x (-3) 12)
      clear * - r27313 b27314 b27315 d27304
      omega
    have d27316 : (x 2 11).toNat = 1 := by
      have r27317 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := by have q := hcov11 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27318 := hb (x (-2) 4)
      have b27319 := hb (x 2 11)
      have b27320 := hb (x 1 1 && x 1 12)
      have b27321 := hb (x 0 2 && x 0 13)
      have b27322 := hb (x (-1) 3 && x (-1) 14)
      clear * - r27317 b27318 b27319 b27320 b27321 b27322 d27276 d27200 g43 g2
      omega
    have d27323 : (x 2 3).toNat = 1 := by
      have r27324 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
      have b27325 := hb (x 2 3)
      have b27326 := hb (x 2 11)
      clear * - r27324 b27325 b27326 d27316
      omega
    have d27327 : (x 5 12).toNat = 0 := by
      have r27328 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27329 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e27330 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b27331 := hb (x 2 3)
      have b27332 := hb (x 3 2)
      have b27333 := hb (x 4 13)
      have b27334 := hb (x 5 12)
      clear * - r27328 e27329 e27330 b27331 b27332 b27333 b27334 d27323
      omega
    have d27335 : (x 4 13).toNat = 0 := by
      have r27336 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27337 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e27338 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b27339 := hb (x 2 3)
      have b27340 := hb (x 3 2)
      have b27341 := hb (x 4 13)
      have b27342 := hb (x 5 12)
      clear * - r27336 e27337 e27338 b27339 b27340 b27341 b27342 d27327 d27323
      omega
    have d27343 : (x 3 2).toNat = 0 := by
      have r27344 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27345 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e27346 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b27347 := hb (x 2 3)
      have b27348 := hb (x 3 2)
      have b27349 := hb (x 4 13)
      have b27350 := hb (x 5 12)
      clear * - r27344 e27345 e27346 b27347 b27348 b27349 b27350 d27327 d27335 d27323
      omega
    have d27351 : (x 1 11).toNat = 1 := by
      have r27352 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27353 := hb (x (-3) 4)
      have b27354 := hb (x 1 11)
      have b27355 := hb (x 0 1 && x 0 12)
      have b27356 := hb (x (-1) 2 && x (-1) 13)
      have b27357 := hb (x (-2) 3 && x (-2) 14)
      clear * - r27352 b27353 b27354 b27355 b27356 b27357 d27192 g42 d27288 d27312
      omega
    have d27358 : (x 1 3).toNat = 1 := by
      have r27359 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
      have b27360 := hb (x 1 3)
      have b27361 := hb (x 1 11)
      clear * - r27359 b27360 b27361 d27351
      omega
    have d27362 : (x 4 12).toNat = 0 := by
      have r27363 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27364 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e27365 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b27366 := hb (x 1 3)
      have b27367 := hb (x 2 2)
      have b27368 := hb (x 3 13)
      have b27369 := hb (x 4 12)
      clear * - r27363 e27364 e27365 b27366 b27367 b27368 b27369 d27358
      omega
    have d27370 : (x 3 13).toNat = 0 := by
      have r27371 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27372 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e27373 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b27374 := hb (x 1 3)
      have b27375 := hb (x 2 2)
      have b27376 := hb (x 3 13)
      have b27377 := hb (x 4 12)
      clear * - r27371 e27372 e27373 b27374 b27375 b27376 b27377 d27362 d27358
      omega
    have d27378 : (x 2 2).toNat = 0 := by
      have r27379 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27380 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e27381 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b27382 := hb (x 1 3)
      have b27383 := hb (x 2 2)
      have b27384 := hb (x 3 13)
      have b27385 := hb (x 4 12)
      clear * - r27379 e27380 e27381 b27382 b27383 b27384 b27385 d27362 d27370 d27358
      omega
    have d27386 : (x 3 1 && x 3 14).toNat = 1 := by
      have r27387 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27388 := hb (x 2 2)
      have b27389 := hb (x 4 13)
      have b27390 := hb (x 3 1 && x 3 14)
      clear * - r27387 b27388 b27389 b27390 d27335 d27378
      omega
    have d27391 : (x 3 14).toNat = 1 := by
      have r27392 := hand2 (x 3 1) (x 3 14)
      have b27393 := hb (x 3 14)
      have b27394 := hb (x 3 1 && x 3 14)
      clear * - r27392 b27393 b27394 d27386
      omega
    have d27395 : (x 2 1).toNat = 0 := by
      have r27396 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27397 := hb (x 2 1)
      have b27398 := hb (x 3 14)
      clear * - r27396 b27397 b27398 d27391
      omega
    have d27399 : (x 2 1 && x 2 14).toNat = 0 := by
      have r27400 := hand1 (x 2 1) (x 2 14)
      have b27401 := hb (x 2 1)
      have b27402 := hb (x 2 1 && x 2 14)
      clear * - r27400 b27401 b27402 d27395
      omega
    have d27403 : (x 1 2).toNat = 1 := by
      have r27404 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27405 := hb (x 1 2)
      have b27406 := hb (x 3 13)
      have b27407 := hb (x 2 1 && x 2 14)
      clear * - r27404 b27405 b27406 b27407 d27370 d27399
      omega
    have d27408 : (x 3 12).toNat = 0 := by
      have r27409 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27410 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e27411 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b27412 := hb (x 0 3)
      have b27413 := hb (x 1 2)
      have b27414 := hb (x 2 13)
      have b27415 := hb (x 3 12)
      clear * - r27409 e27410 e27411 b27412 b27413 b27414 b27415 d27403
      omega
    have d27416 : (x 2 13).toNat = 0 := by
      have r27417 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27418 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e27419 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b27420 := hb (x 0 3)
      have b27421 := hb (x 1 2)
      have b27422 := hb (x 2 13)
      have b27423 := hb (x 3 12)
      clear * - r27417 e27418 e27419 b27420 b27421 b27422 b27423 d27408 d27403
      omega
    have d27424 : (x 0 3).toNat = 0 := by
      have r27425 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27426 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e27427 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b27428 := hb (x 0 3)
      have b27429 := hb (x 1 2)
      have b27430 := hb (x 2 13)
      have b27431 := hb (x 3 12)
      clear * - r27425 e27426 e27427 b27428 b27429 b27430 b27431 d27408 d27416 d27403
      omega
    have d27432 : (x 0 3 && x 0 14).toNat = 0 := by
      have r27433 := hand1 (x 0 3) (x 0 14)
      have b27434 := hb (x 0 3)
      have b27435 := hb (x 0 3 && x 0 14)
      clear * - r27433 b27434 b27435 d27424
      omega
    have d27436 : (x 3 11).toNat = 1 := by
      have r27437 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27438 := hb (x (-1) 4)
      have b27439 := hb (x 3 11)
      have b27440 := hb (x 2 1 && x 2 12)
      have b27441 := hb (x 1 2 && x 1 13)
      have b27442 := hb (x 0 3 && x 0 14)
      clear * - r27437 b27438 b27439 b27440 b27441 b27442 g44 g45 d27432 d27300
      omega
    have d27443 : (x 3 3).toNat = 1 := by
      have r27444 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b27445 := hb (x 3 3)
      have b27446 := hb (x 3 11)
      clear * - r27444 b27445 b27446 d27436
      omega
    have d27447 : (x 6 12).toNat = 0 := by
      have r27448 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27449 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e27450 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b27451 := hb (x 3 3)
      have b27452 := hb (x 4 2)
      have b27453 := hb (x 5 13)
      have b27454 := hb (x 6 12)
      clear * - r27448 e27449 e27450 b27451 b27452 b27453 b27454 d27443
      omega
    have d27455 : (x 5 13).toNat = 0 := by
      have r27456 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27457 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e27458 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b27459 := hb (x 3 3)
      have b27460 := hb (x 4 2)
      have b27461 := hb (x 5 13)
      have b27462 := hb (x 6 12)
      clear * - r27456 e27457 e27458 b27459 b27460 b27461 b27462 d27447 d27443
      omega
    have d27463 : (x 4 1 && x 4 14).toNat = 1 := by
      have r27464 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27465 := hb (x 3 2)
      have b27466 := hb (x 5 13)
      have b27467 := hb (x 4 1 && x 4 14)
      clear * - r27464 b27465 b27466 b27467 d27455 d27343
      omega
    have d27468 : (x 4 14).toNat = 1 := by
      have r27469 := hand2 (x 4 1) (x 4 14)
      have b27470 := hb (x 4 14)
      have b27471 := hb (x 4 1 && x 4 14)
      clear * - r27469 b27470 b27471 d27463
      omega
    have d27472 : (x 3 1).toNat = 0 := by
      have r27473 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27474 := hb (x 3 1)
      have b27475 := hb (x 4 14)
      clear * - r27473 b27474 b27475 d27468
      omega
    have r27476 := hand1 (x 3 1) (x 3 14)
    have b27477 := hb (x 3 1)
    have b27478 := hb (x 3 1 && x 3 14)
    linarith only [r27476, b27477, b27478, d27386, d27472]
  · have f27479 : (x 0 1).toNat = 1 := by rw [h27186]; rfl
    have d27480 : (x 1 14).toNat = 0 := by
      have r27481 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27482 := hb (x 0 1)
      have b27483 := hb (x 1 14)
      clear * - r27481 b27482 b27483 f27479
      omega
    have d27484 : (x 1 3 && x 1 14).toNat = 0 := by
      have r27485 := hand2 (x 1 3) (x 1 14)
      have b27486 := hb (x 1 14)
      have b27487 := hb (x 1 3 && x 1 14)
      clear * - r27485 b27486 b27487 d27480
      omega
    have d27488 : (x 1 4 && x 1 14).toNat = 0 := by
      have r27489 := hand2 (x 1 4) (x 1 14)
      have b27490 := hb (x 1 14)
      have b27491 := hb (x 1 4 && x 1 14)
      clear * - r27489 b27490 b27491 d27480
      omega
    have d27492 : (x 1 6).toNat = 0 := by
      have r27493 : (x 1 6).toNat ≤ (x 1 14).toNat := himp _ _ (hp6 1)
      have b27494 := hb (x 1 6)
      have b27495 := hb (x 1 14)
      clear * - r27493 b27494 b27495 d27480
      omega
    have d27496 : (x 1 2).toNat = 0 := by
      have r27497 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
      have b27498 := hb (x 1 2)
      have b27499 := hb (x 1 14)
      clear * - r27497 b27498 b27499 d27480
      omega
    have d27500 : (x 1 2 && x 1 11).toNat = 0 := by
      have r27501 := hand1 (x 1 2) (x 1 11)
      have b27502 := hb (x 1 2)
      have b27503 := hb (x 1 2 && x 1 11)
      clear * - r27501 b27502 b27503 d27496
      omega
    have d27504 : (x 1 10).toNat = 0 := by
      have r27505 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
      have b27506 := hb (x 1 2)
      have b27507 := hb (x 1 10)
      clear * - r27505 b27506 b27507 d27496
      omega
    have d27508 : (x 1 1 && x 1 10).toNat = 0 := by
      have r27509 := hand2 (x 1 1) (x 1 10)
      have b27510 := hb (x 1 10)
      have b27511 := hb (x 1 1 && x 1 10)
      clear * - r27509 b27510 b27511 d27504
      omega
    have d27512 : (x 2 9).toNat = 1 := by
      have r27513 : 1 ≤ (x 2 9).toNat + (x 1 1 && x 1 10).toNat + (x 0 2 && x 0 11).toNat + (x (-1) 3 && x (-1) 12).toNat + (x (-2) 4 && x (-2) 13).toNat + (x (-3) 5 && x (-3) 14).toNat + (x (-4) 6).toNat := by have q := hcov9 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27514 := hb (x (-4) 6)
      have b27515 := hb (x 2 9)
      have b27516 := hb (x 1 1 && x 1 10)
      have b27517 := hb (x 0 2 && x 0 11)
      have b27518 := hb (x (-1) 3 && x (-1) 12)
      have b27519 := hb (x (-2) 4 && x (-2) 13)
      have b27520 := hb (x (-3) 5 && x (-3) 14)
      clear * - r27513 b27514 b27515 b27516 b27517 b27518 b27519 b27520 d27508 g28 g29 g30 g31 g0
      omega
    have d27521 : (x 2 1).toNat = 1 := by
      have r27522 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
      have b27523 := hb (x 2 1)
      have b27524 := hb (x 2 9)
      clear * - r27522 b27523 b27524 d27512
      omega
    have d27525 : (x 3 14).toNat = 0 := by
      have r27526 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b27527 := hb (x 2 1)
      have b27528 := hb (x 3 14)
      clear * - r27526 b27527 b27528 d27521
      omega
    have d27529 : (x 3 3 && x 3 14).toNat = 0 := by
      have r27530 := hand2 (x 3 3) (x 3 14)
      have b27531 := hb (x 3 14)
      have b27532 := hb (x 3 3 && x 3 14)
      clear * - r27530 b27531 b27532 d27525
      omega
    have d27533 : (x 3 2).toNat = 0 := by
      have r27534 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b27535 := hb (x 3 2)
      have b27536 := hb (x 3 14)
      clear * - r27534 b27535 b27536 d27525
      omega
    have d27537 : (x 3 2 && x 3 12).toNat = 0 := by
      have r27538 := hand1 (x 3 2) (x 3 12)
      have b27539 := hb (x 3 2)
      have b27540 := hb (x 3 2 && x 3 12)
      clear * - r27538 b27539 b27540 d27533
      omega
    have d27541 : (x 3 10).toNat = 0 := by
      have r27542 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
      have b27543 := hb (x 3 2)
      have b27544 := hb (x 3 10)
      clear * - r27542 b27543 b27544 d27533
      omega
    have d27545 : (x 3 1 && x 3 10).toNat = 0 := by
      have r27546 := hand2 (x 3 1) (x 3 10)
      have b27547 := hb (x 3 10)
      have b27548 := hb (x 3 1 && x 3 10)
      clear * - r27546 b27547 b27548 d27541
      omega
    have d27549 : (x 3 8).toNat = 0 := by
      have r27550 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27551 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e27552 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e27553 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e27554 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e27555 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e27556 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b27557 := hb (x (-4) 7)
      have b27558 := hb (x (-3) 6)
      have b27559 := hb (x (-2) 5)
      have b27560 := hb (x (-1) 4)
      have b27561 := hb (x 0 11)
      have b27562 := hb (x 1 10)
      have b27563 := hb (x 2 9)
      have b27564 := hb (x 3 8)
      clear * - r27550 e27551 e27552 e27553 e27554 e27555 e27556 b27557 b27558 b27559 b27560 b27561 b27562 b27563 b27564 d27512 d27504 g7
      omega
    have d27565 : (x (-1) 4).toNat = 0 := by
      have r27566 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27567 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e27568 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e27569 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e27570 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e27571 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e27572 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b27573 := hb (x (-4) 7)
      have b27574 := hb (x (-3) 6)
      have b27575 := hb (x (-2) 5)
      have b27576 := hb (x (-1) 4)
      have b27577 := hb (x 0 11)
      have b27578 := hb (x 1 10)
      have b27579 := hb (x 2 9)
      have b27580 := hb (x 3 8)
      clear * - r27566 e27567 e27568 e27569 e27570 e27571 e27572 b27573 b27574 b27575 b27576 b27577 b27578 b27579 b27580 d27549 d27512 d27504 g7
      omega
    have d27581 : (x (-2) 5).toNat = 0 := by
      have r27582 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27583 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e27584 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e27585 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e27586 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e27587 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e27588 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b27589 := hb (x (-4) 7)
      have b27590 := hb (x (-3) 6)
      have b27591 := hb (x (-2) 5)
      have b27592 := hb (x (-1) 4)
      have b27593 := hb (x 0 11)
      have b27594 := hb (x 1 10)
      have b27595 := hb (x 2 9)
      have b27596 := hb (x 3 8)
      clear * - r27582 e27583 e27584 e27585 e27586 e27587 e27588 b27589 b27590 b27591 b27592 b27593 b27594 b27595 b27596 d27549 d27512 d27504 g7 d27565
      omega
    have d27597 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
      have r27598 := hand1 (x (-2) 5) (x (-2) 14)
      have b27599 := hb (x (-2) 5)
      have b27600 := hb (x (-2) 5 && x (-2) 14)
      clear * - r27598 b27599 b27600 d27581
      omega
    have d27601 : (x (-3) 6).toNat = 0 := by
      have r27602 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e27603 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e27604 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e27605 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e27606 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e27607 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e27608 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b27609 := hb (x (-4) 7)
      have b27610 := hb (x (-3) 6)
      have b27611 := hb (x (-2) 5)
      have b27612 := hb (x (-1) 4)
      have b27613 := hb (x 0 11)
      have b27614 := hb (x 1 10)
      have b27615 := hb (x 2 9)
      have b27616 := hb (x 3 8)
      clear * - r27602 e27603 e27604 e27605 e27606 e27607 e27608 b27609 b27610 b27611 b27612 b27613 b27614 b27615 b27616 d27549 d27512 d27504 g7 d27565 d27581
      omega
    cases h27617 : x 0 3
    · have f27618 : (x 0 3).toNat = 0 := by rw [h27617]; rfl
      have d27619 : (x 0 3 && x 0 14).toNat = 0 := by
        have r27620 := hand1 (x 0 3) (x 0 14)
        have b27621 := hb (x 0 3)
        have b27622 := hb (x 0 3 && x 0 14)
        clear * - r27620 b27621 b27622 f27618
        omega
      have d27623 : (x 3 11).toNat = 1 := by
        have r27624 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27625 := hb (x (-1) 4)
        have b27626 := hb (x 3 11)
        have b27627 := hb (x 2 1 && x 2 12)
        have b27628 := hb (x 1 2 && x 1 13)
        have b27629 := hb (x 0 3 && x 0 14)
        clear * - r27624 b27625 b27626 b27627 b27628 b27629 g44 g45 d27619 d27565
        omega
      have d27630 : (x 3 3).toNat = 1 := by
        have r27631 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
        have b27632 := hb (x 3 3)
        have b27633 := hb (x 3 11)
        clear * - r27631 b27632 b27633 d27623
        omega
      have d27634 : (x 6 12).toNat = 0 := by
        have r27635 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27636 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e27637 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b27638 := hb (x 3 3)
        have b27639 := hb (x 4 2)
        have b27640 := hb (x 5 13)
        have b27641 := hb (x 6 12)
        clear * - r27635 e27636 e27637 b27638 b27639 b27640 b27641 d27630
        omega
      have d27642 : (x 6 1 && x 6 12).toNat = 0 := by
        have r27643 := hand2 (x 6 1) (x 6 12)
        have b27644 := hb (x 6 12)
        have b27645 := hb (x 6 1 && x 6 12)
        clear * - r27643 b27644 b27645 d27634
        omega
      have d27646 : (x 6 4).toNat = 0 := by
        have r27647 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
        have b27648 := hb (x 6 4)
        have b27649 := hb (x 6 12)
        clear * - r27647 b27648 b27649 d27634
        omega
      have d27650 : (x 5 13).toNat = 0 := by
        have r27651 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27652 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e27653 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b27654 := hb (x 3 3)
        have b27655 := hb (x 4 2)
        have b27656 := hb (x 5 13)
        have b27657 := hb (x 6 12)
        clear * - r27651 e27652 e27653 b27654 b27655 b27656 b27657 d27634 d27630
        omega
      have d27658 : (x 5 2 && x 5 13).toNat = 0 := by
        have r27659 := hand2 (x 5 2) (x 5 13)
        have b27660 := hb (x 5 13)
        have b27661 := hb (x 5 2 && x 5 13)
        clear * - r27659 b27660 b27661 d27650
        omega
      have d27662 : (x 4 1 && x 4 14).toNat = 1 := by
        have r27663 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27664 := hb (x 3 2)
        have b27665 := hb (x 5 13)
        have b27666 := hb (x 4 1 && x 4 14)
        clear * - r27663 b27664 b27665 b27666 d27650 d27533
        omega
      have d27667 : (x 4 14).toNat = 1 := by
        have r27668 := hand2 (x 4 1) (x 4 14)
        have b27669 := hb (x 4 14)
        have b27670 := hb (x 4 1 && x 4 14)
        clear * - r27668 b27669 b27670 d27662
        omega
      have d27671 : (x 3 1).toNat = 0 := by
        have r27672 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27673 := hb (x 3 1)
        have b27674 := hb (x 4 14)
        clear * - r27672 b27673 b27674 d27667
        omega
      have d27675 : (x 3 1 && x 3 12).toNat = 0 := by
        have r27676 := hand1 (x 3 1) (x 3 12)
        have b27677 := hb (x 3 1)
        have b27678 := hb (x 3 1 && x 3 12)
        clear * - r27676 b27677 b27678 d27671
        omega
      have d27679 : (x 4 1).toNat = 1 := by
        have r27680 := hand1 (x 4 1) (x 4 14)
        have b27681 := hb (x 4 1)
        have b27682 := hb (x 4 1 && x 4 14)
        clear * - r27680 b27681 b27682 d27662
        omega
      have d27683 : (x 5 14).toNat = 0 := by
        have r27684 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27685 := hb (x 4 1)
        have b27686 := hb (x 5 14)
        clear * - r27684 b27685 b27686 d27679
        omega
      have d27687 : (x 5 1 && x 5 14).toNat = 0 := by
        have r27688 := hand2 (x 5 1) (x 5 14)
        have b27689 := hb (x 5 14)
        have b27690 := hb (x 5 1 && x 5 14)
        clear * - r27688 b27689 b27690 d27683
        omega
      have d27691 : (x 5 2).toNat = 0 := by
        have r27692 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
        have b27693 := hb (x 5 2)
        have b27694 := hb (x 5 14)
        clear * - r27692 b27693 b27694 d27683
        omega
      have d27695 : (x 4 2).toNat = 0 := by
        have r27696 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27697 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
        have e27698 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
        have b27699 := hb (x 3 3)
        have b27700 := hb (x 4 2)
        have b27701 := hb (x 5 13)
        have b27702 := hb (x 6 12)
        clear * - r27696 e27697 e27698 b27699 b27700 b27701 b27702 d27634 d27650 d27630
        omega
      have d27703 : (x 4 2 && x 4 13).toNat = 0 := by
        have r27704 := hand1 (x 4 2) (x 4 13)
        have b27705 := hb (x 4 2)
        have b27706 := hb (x 4 2 && x 4 13)
        clear * - r27704 b27705 b27706 d27695
        omega
      have d27707 : (x 6 13).toNat = 1 := by
        have r27708 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27709 := hb (x 4 2)
        have b27710 := hb (x 6 13)
        have b27711 := hb (x 5 1 && x 5 14)
        clear * - r27708 b27709 b27710 b27711 d27687 d27695
        omega
      have d27712 : (x 6 1).toNat = 1 := by
        have r27713 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
        have b27714 := hb (x 6 1)
        have b27715 := hb (x 6 13)
        clear * - r27713 b27714 b27715 d27707
        omega
      have d27716 : (x 7 14).toNat = 0 := by
        have r27717 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27718 := hb (x 6 1)
        have b27719 := hb (x 7 14)
        clear * - r27717 b27718 b27719 d27712
        omega
      have d27720 : (x 7 3 && x 7 14).toNat = 0 := by
        have r27721 := hand2 (x 7 3) (x 7 14)
        have b27722 := hb (x 7 14)
        have b27723 := hb (x 7 3 && x 7 14)
        clear * - r27721 b27722 b27723 d27716
        omega
      have d27724 : (x 7 2).toNat = 0 := by
        have r27725 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
        have b27726 := hb (x 7 2)
        have b27727 := hb (x 7 14)
        clear * - r27725 b27726 b27727 d27716
        omega
      have d27728 : (x 7 12).toNat = 0 := by
        have r27729 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27730 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e27731 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b27732 := hb (x 4 3)
        have b27733 := hb (x 5 2)
        have b27734 := hb (x 6 13)
        have b27735 := hb (x 7 12)
        clear * - r27729 e27730 e27731 b27732 b27733 b27734 b27735 d27707 d27691
        omega
      have d27736 : (x 7 4).toNat = 0 := by
        have r27737 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
        have b27738 := hb (x 7 4)
        have b27739 := hb (x 7 12)
        clear * - r27737 b27738 b27739 d27728
        omega
      have d27740 : (x 4 3).toNat = 0 := by
        have r27741 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27742 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e27743 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b27744 := hb (x 4 3)
        have b27745 := hb (x 5 2)
        have b27746 := hb (x 6 13)
        have b27747 := hb (x 7 12)
        clear * - r27741 e27742 e27743 b27744 b27745 b27746 b27747 d27728 d27707 d27691
        omega
      have d27748 : (x 4 3 && x 4 14).toNat = 0 := by
        have r27749 := hand1 (x 4 3) (x 4 14)
        have b27750 := hb (x 4 3)
        have b27751 := hb (x 4 3 && x 4 14)
        clear * - r27749 b27750 b27751 d27740
        omega
      have d27752 : (x 4 11).toNat = 0 := by
        have r27753 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
        have b27754 := hb (x 4 3)
        have b27755 := hb (x 4 11)
        clear * - r27753 b27754 b27755 d27740
        omega
      have d27756 : (x 2 2 && x 2 13).toNat = 1 := by
        have r27757 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27758 := hb (x 0 4)
        have b27759 := hb (x 4 11)
        have b27760 := hb (x 3 1 && x 3 12)
        have b27761 := hb (x 2 2 && x 2 13)
        have b27762 := hb (x 1 3 && x 1 14)
        clear * - r27757 b27758 b27759 b27760 b27761 b27762 d27752 d27675 d27484 g6
        omega
      have d27763 : (x 2 13).toNat = 1 := by
        have r27764 := hand2 (x 2 2) (x 2 13)
        have b27765 := hb (x 2 13)
        have b27766 := hb (x 2 2 && x 2 13)
        clear * - r27764 b27765 b27766 d27756
        omega
      have d27767 : (x 3 12).toNat = 0 := by
        have r27768 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27769 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e27770 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b27771 := hb (x 0 3)
        have b27772 := hb (x 1 2)
        have b27773 := hb (x 2 13)
        have b27774 := hb (x 3 12)
        clear * - r27768 e27769 e27770 b27771 b27772 b27773 b27774 d27763 d27496 f27618
        omega
      have d27775 : (x 3 4).toNat = 0 := by
        have r27776 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
        have b27777 := hb (x 3 4)
        have b27778 := hb (x 3 12)
        clear * - r27776 b27777 b27778 d27767
        omega
      have d27779 : (x 7 11).toNat = 1 := by
        have r27780 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27781 := hb (x 3 4)
        have b27782 := hb (x 7 11)
        have b27783 := hb (x 6 1 && x 6 12)
        have b27784 := hb (x 5 2 && x 5 13)
        have b27785 := hb (x 4 3 && x 4 14)
        clear * - r27780 b27781 b27782 b27783 b27784 b27785 d27642 d27658 d27748 d27775
        omega
      have d27786 : (x 7 3).toNat = 1 := by
        have r27787 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
        have b27788 := hb (x 7 3)
        have b27789 := hb (x 7 11)
        clear * - r27787 b27788 b27789 d27779
        omega
      have d27790 : (x 10 12).toNat = 0 := by
        have r27791 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27792 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e27793 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b27794 := hb (x 7 3)
        have b27795 := hb (x 8 2)
        have b27796 := hb (x 9 13)
        have b27797 := hb (x 10 12)
        clear * - r27791 e27792 e27793 b27794 b27795 b27796 b27797 d27786
        omega
      have d27798 : (x 10 1 && x 10 12).toNat = 0 := by
        have r27799 := hand2 (x 10 1) (x 10 12)
        have b27800 := hb (x 10 12)
        have b27801 := hb (x 10 1 && x 10 12)
        clear * - r27799 b27800 b27801 d27790
        omega
      have d27802 : (x 10 4).toNat = 0 := by
        have r27803 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
        have b27804 := hb (x 10 4)
        have b27805 := hb (x 10 12)
        clear * - r27803 b27804 b27805 d27790
        omega
      have d27806 : (x 9 13).toNat = 0 := by
        have r27807 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27808 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e27809 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b27810 := hb (x 7 3)
        have b27811 := hb (x 8 2)
        have b27812 := hb (x 9 13)
        have b27813 := hb (x 10 12)
        clear * - r27807 e27808 e27809 b27810 b27811 b27812 b27813 d27790 d27786
        omega
      have d27814 : (x 9 2 && x 9 13).toNat = 0 := by
        have r27815 := hand2 (x 9 2) (x 9 13)
        have b27816 := hb (x 9 13)
        have b27817 := hb (x 9 2 && x 9 13)
        clear * - r27815 b27816 b27817 d27806
        omega
      have d27818 : (x 8 1 && x 8 14).toNat = 1 := by
        have r27819 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27820 := hb (x 7 2)
        have b27821 := hb (x 9 13)
        have b27822 := hb (x 8 1 && x 8 14)
        clear * - r27819 b27820 b27821 b27822 d27806 d27724
        omega
      have d27823 : (x 8 14).toNat = 1 := by
        have r27824 := hand2 (x 8 1) (x 8 14)
        have b27825 := hb (x 8 14)
        have b27826 := hb (x 8 1 && x 8 14)
        clear * - r27824 b27825 b27826 d27818
        omega
      have d27827 : (x 7 1).toNat = 0 := by
        have r27828 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27829 := hb (x 7 1)
        have b27830 := hb (x 8 14)
        clear * - r27828 b27829 b27830 d27823
        omega
      have d27831 : (x 7 13).toNat = 0 := by
        have r27832 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
        have b27833 := hb (x 7 1)
        have b27834 := hb (x 7 13)
        clear * - r27832 b27833 b27834 d27827
        omega
      have d27835 : (x 6 1 && x 6 14).toNat = 1 := by
        have r27836 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27837 := hb (x 5 2)
        have b27838 := hb (x 7 13)
        have b27839 := hb (x 6 1 && x 6 14)
        clear * - r27836 b27837 b27838 b27839 d27831 d27691
        omega
      have d27840 : (x 6 14).toNat = 1 := by
        have r27841 := hand2 (x 6 1) (x 6 14)
        have b27842 := hb (x 6 14)
        have b27843 := hb (x 6 1 && x 6 14)
        clear * - r27841 b27842 b27843 d27835
        omega
      have d27844 : (x 5 1).toNat = 0 := by
        have r27845 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27846 := hb (x 5 1)
        have b27847 := hb (x 6 14)
        clear * - r27845 b27846 b27847 d27840
        omega
      have d27848 : (x 5 1 && x 5 12).toNat = 0 := by
        have r27849 := hand1 (x 5 1) (x 5 12)
        have b27850 := hb (x 5 1)
        have b27851 := hb (x 5 1 && x 5 12)
        clear * - r27849 b27850 b27851 d27844
        omega
      have d27852 : (x 6 11).toNat = 1 := by
        have r27853 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27854 := hb (x 2 4)
        have b27855 := hb (x 6 11)
        have b27856 := hb (x 5 1 && x 5 12)
        have b27857 := hb (x 4 2 && x 4 13)
        have b27858 := hb (x 3 3 && x 3 14)
        clear * - r27853 b27854 b27855 b27856 b27857 b27858 d27848 d27703 d27529 g12
        omega
      have d27859 : (x 6 3).toNat = 1 := by
        have r27860 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
        have b27861 := hb (x 6 3)
        have b27862 := hb (x 6 11)
        clear * - r27860 b27861 b27862 d27852
        omega
      have d27863 : (x 9 12).toNat = 0 := by
        have r27864 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27865 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e27866 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b27867 := hb (x 6 3)
        have b27868 := hb (x 7 2)
        have b27869 := hb (x 8 13)
        have b27870 := hb (x 9 12)
        clear * - r27864 e27865 e27866 b27867 b27868 b27869 b27870 d27724 d27859
        omega
      have d27871 : (x 9 1 && x 9 12).toNat = 0 := by
        have r27872 := hand2 (x 9 1) (x 9 12)
        have b27873 := hb (x 9 12)
        have b27874 := hb (x 9 1 && x 9 12)
        clear * - r27872 b27873 b27874 d27863
        omega
      have d27875 : (x 8 13).toNat = 0 := by
        have r27876 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27877 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e27878 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b27879 := hb (x 6 3)
        have b27880 := hb (x 7 2)
        have b27881 := hb (x 8 13)
        have b27882 := hb (x 9 12)
        clear * - r27876 e27877 e27878 b27879 b27880 b27881 b27882 d27863 d27724 d27859
        omega
      have d27883 : (x 8 2 && x 8 13).toNat = 0 := by
        have r27884 := hand2 (x 8 2) (x 8 13)
        have b27885 := hb (x 8 13)
        have b27886 := hb (x 8 2 && x 8 13)
        clear * - r27884 b27885 b27886 d27875
        omega
      have d27887 : (x 10 11).toNat = 1 := by
        have r27888 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27889 := hb (x 6 4)
        have b27890 := hb (x 10 11)
        have b27891 := hb (x 9 1 && x 9 12)
        have b27892 := hb (x 8 2 && x 8 13)
        have b27893 := hb (x 7 3 && x 7 14)
        clear * - r27888 b27889 b27890 b27891 b27892 b27893 d27871 d27883 d27720 d27646
        omega
      have d27894 : (x 10 3).toNat = 1 := by
        have r27895 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
        have b27896 := hb (x 10 3)
        have b27897 := hb (x 10 11)
        clear * - r27895 b27896 b27897 d27887
        omega
      have d27898 : (x 13 12).toNat = 0 := by
        have r27899 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27900 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e27901 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b27902 := hb (x 10 3)
        have b27903 := hb (x 11 2)
        have b27904 := hb (x 12 13)
        have b27905 := hb (x 13 12)
        clear * - r27899 e27900 e27901 b27902 b27903 b27904 b27905 d27894
        omega
      have d27906 : (x 13 1 && x 13 12).toNat = 0 := by
        have r27907 := hand2 (x 13 1) (x 13 12)
        have b27908 := hb (x 13 12)
        have b27909 := hb (x 13 1 && x 13 12)
        clear * - r27907 b27908 b27909 d27898
        omega
      have d27910 : (x 12 13).toNat = 0 := by
        have r27911 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27912 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e27913 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b27914 := hb (x 10 3)
        have b27915 := hb (x 11 2)
        have b27916 := hb (x 12 13)
        have b27917 := hb (x 13 12)
        clear * - r27911 e27912 e27913 b27914 b27915 b27916 b27917 d27898 d27894
        omega
      have d27918 : (x 12 2 && x 12 13).toNat = 0 := by
        have r27919 := hand2 (x 12 2) (x 12 13)
        have b27920 := hb (x 12 13)
        have b27921 := hb (x 12 2 && x 12 13)
        clear * - r27919 b27920 b27921 d27910
        omega
      have d27922 : (x 11 2).toNat = 0 := by
        have r27923 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27924 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e27925 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b27926 := hb (x 10 3)
        have b27927 := hb (x 11 2)
        have b27928 := hb (x 12 13)
        have b27929 := hb (x 13 12)
        clear * - r27923 e27924 e27925 b27926 b27927 b27928 b27929 d27898 d27910 d27894
        omega
      have d27930 : (x 8 1).toNat = 1 := by
        have r27931 := hand1 (x 8 1) (x 8 14)
        have b27932 := hb (x 8 1)
        have b27933 := hb (x 8 1 && x 8 14)
        clear * - r27931 b27932 b27933 d27818
        omega
      have d27934 : (x 9 14).toNat = 0 := by
        have r27935 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27936 := hb (x 8 1)
        have b27937 := hb (x 9 14)
        clear * - r27935 b27936 b27937 d27930
        omega
      have d27938 : (x 9 1 && x 9 14).toNat = 0 := by
        have r27939 := hand2 (x 9 1) (x 9 14)
        have b27940 := hb (x 9 14)
        have b27941 := hb (x 9 1 && x 9 14)
        clear * - r27939 b27940 b27941 d27934
        omega
      have d27942 : (x 9 2).toNat = 0 := by
        have r27943 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
        have b27944 := hb (x 9 2)
        have b27945 := hb (x 9 14)
        clear * - r27943 b27944 b27945 d27934
        omega
      have d27946 : (x 8 2).toNat = 0 := by
        have r27947 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27948 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e27949 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b27950 := hb (x 7 3)
        have b27951 := hb (x 8 2)
        have b27952 := hb (x 9 13)
        have b27953 := hb (x 10 12)
        clear * - r27947 e27948 e27949 b27950 b27951 b27952 b27953 d27790 d27806 d27786
        omega
      have d27954 : (x 10 13).toNat = 1 := by
        have r27955 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27956 := hb (x 8 2)
        have b27957 := hb (x 10 13)
        have b27958 := hb (x 9 1 && x 9 14)
        clear * - r27955 b27956 b27957 b27958 d27938 d27946
        omega
      have d27959 : (x 10 1).toNat = 1 := by
        have r27960 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
        have b27961 := hb (x 10 1)
        have b27962 := hb (x 10 13)
        clear * - r27960 b27961 b27962 d27954
        omega
      have d27963 : (x 11 14).toNat = 0 := by
        have r27964 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27965 := hb (x 10 1)
        have b27966 := hb (x 11 14)
        clear * - r27964 b27965 b27966 d27959
        omega
      have d27967 : (x 11 1 && x 11 14).toNat = 0 := by
        have r27968 := hand2 (x 11 1) (x 11 14)
        have b27969 := hb (x 11 14)
        have b27970 := hb (x 11 1 && x 11 14)
        clear * - r27968 b27969 b27970 d27963
        omega
      have d27971 : (x 10 2).toNat = 1 := by
        have r27972 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b27973 := hb (x 10 2)
        have b27974 := hb (x 12 13)
        have b27975 := hb (x 11 1 && x 11 14)
        clear * - r27972 b27973 b27974 b27975 d27910 d27967
        omega
      have d27976 : (x 12 12).toNat = 0 := by
        have r27977 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27978 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e27979 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b27980 := hb (x 9 3)
        have b27981 := hb (x 10 2)
        have b27982 := hb (x 11 13)
        have b27983 := hb (x 12 12)
        clear * - r27977 e27978 e27979 b27980 b27981 b27982 b27983 d27971
        omega
      have d27984 : (x 12 4).toNat = 0 := by
        have r27985 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
        have b27986 := hb (x 12 4)
        have b27987 := hb (x 12 12)
        clear * - r27985 b27986 b27987 d27976
        omega
      have d27988 : (x 12 4 && x 12 14).toNat = 0 := by
        have r27989 := hand1 (x 12 4) (x 12 14)
        have b27990 := hb (x 12 4)
        have b27991 := hb (x 12 4 && x 12 14)
        clear * - r27989 b27990 b27991 d27984
        omega
      have d27992 : (x 11 13).toNat = 0 := by
        have r27993 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e27994 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e27995 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b27996 := hb (x 9 3)
        have b27997 := hb (x 10 2)
        have b27998 := hb (x 11 13)
        have b27999 := hb (x 12 12)
        clear * - r27993 e27994 e27995 b27996 b27997 b27998 b27999 d27976 d27971
        omega
      have d28000 : (x 11 5).toNat = 0 := by
        have r28001 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
        have b28002 := hb (x 11 5)
        have b28003 := hb (x 11 13)
        clear * - r28001 b28002 b28003 d27992
        omega
      have d28004 : (x 11 3 && x 11 14).toNat = 0 := by
        have r28005 := hand2 (x 11 3) (x 11 14)
        have b28006 := hb (x 11 14)
        have b28007 := hb (x 11 3 && x 11 14)
        clear * - r28005 b28006 b28007 d27963
        omega
      have d28008 : (x 14 11).toNat = 1 := by
        have r28009 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b28010 := hb (x 10 4)
        have b28011 := hb (x 14 11)
        have b28012 := hb (x 13 1 && x 13 12)
        have b28013 := hb (x 12 2 && x 12 13)
        have b28014 := hb (x 11 3 && x 11 14)
        clear * - r28009 b28010 b28011 b28012 b28013 b28014 d27906 d27918 d28004 d27802
        omega
      have d28015 : (x 14 3).toNat = 1 := by
        have r28016 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
        have b28017 := hb (x 14 3)
        have b28018 := hb (x 14 11)
        clear * - r28016 b28017 b28018 d28008
        omega
      have d28019 : (x 17 12).toNat = 0 := by
        have r28020 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28021 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e28022 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b28023 := hb (x 14 3)
        have b28024 := hb (x 15 2)
        have b28025 := hb (x 16 13)
        have b28026 := hb (x 17 12)
        clear * - r28020 e28021 e28022 b28023 b28024 b28025 b28026 d28015
        omega
      have d28027 : (x 16 13).toNat = 0 := by
        have r28028 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28029 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e28030 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b28031 := hb (x 14 3)
        have b28032 := hb (x 15 2)
        have b28033 := hb (x 16 13)
        have b28034 := hb (x 17 12)
        clear * - r28028 e28029 e28030 b28031 b28032 b28033 b28034 d28019 d28015
        omega
      have d28035 : (x 15 2).toNat = 0 := by
        have r28036 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28037 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e28038 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b28039 := hb (x 14 3)
        have b28040 := hb (x 15 2)
        have b28041 := hb (x 16 13)
        have b28042 := hb (x 17 12)
        clear * - r28036 e28037 e28038 b28039 b28040 b28041 b28042 d28019 d28027 d28015
        omega
      have d28043 : (x 11 12).toNat = 0 := by
        have r28044 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28045 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e28046 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b28047 := hb (x 8 3)
        have b28048 := hb (x 9 2)
        have b28049 := hb (x 10 13)
        have b28050 := hb (x 11 12)
        clear * - r28044 e28045 e28046 b28047 b28048 b28049 b28050 d27954 d27942
        omega
      have d28051 : (x 11 4).toNat = 0 := by
        have r28052 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
        have b28053 := hb (x 11 4)
        have b28054 := hb (x 11 12)
        clear * - r28052 b28053 b28054 d28043
        omega
      have d28055 : (x 8 3).toNat = 0 := by
        have r28056 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28057 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e28058 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b28059 := hb (x 8 3)
        have b28060 := hb (x 9 2)
        have b28061 := hb (x 10 13)
        have b28062 := hb (x 11 12)
        clear * - r28056 e28057 e28058 b28059 b28060 b28061 b28062 d28043 d27954 d27942
        omega
      have d28063 : (x 8 3 && x 8 14).toNat = 0 := by
        have r28064 := hand1 (x 8 3) (x 8 14)
        have b28065 := hb (x 8 3)
        have b28066 := hb (x 8 3 && x 8 14)
        clear * - r28064 b28065 b28066 d28055
        omega
      have d28067 : (x 11 11).toNat = 1 := by
        have r28068 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b28069 := hb (x 7 4)
        have b28070 := hb (x 11 11)
        have b28071 := hb (x 10 1 && x 10 12)
        have b28072 := hb (x 9 2 && x 9 13)
        have b28073 := hb (x 8 3 && x 8 14)
        clear * - r28068 b28069 b28070 b28071 b28072 b28073 d27798 d27814 d28063 d27736
        omega
      have d28074 : (x 11 3).toNat = 1 := by
        have r28075 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
        have b28076 := hb (x 11 3)
        have b28077 := hb (x 11 11)
        clear * - r28075 b28076 b28077 d28067
        omega
      have d28078 : (x 14 12).toNat = 0 := by
        have r28079 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28080 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e28081 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b28082 := hb (x 11 3)
        have b28083 := hb (x 12 2)
        have b28084 := hb (x 13 13)
        have b28085 := hb (x 14 12)
        clear * - r28079 e28080 e28081 b28082 b28083 b28084 b28085 d28074
        omega
      have d28086 : (x 14 1 && x 14 12).toNat = 0 := by
        have r28087 := hand2 (x 14 1) (x 14 12)
        have b28088 := hb (x 14 12)
        have b28089 := hb (x 14 1 && x 14 12)
        clear * - r28087 b28088 b28089 d28078
        omega
      have d28090 : (x 14 2 && x 14 12).toNat = 0 := by
        have r28091 := hand2 (x 14 2) (x 14 12)
        have b28092 := hb (x 14 12)
        have b28093 := hb (x 14 2 && x 14 12)
        clear * - r28091 b28092 b28093 d28078
        omega
      have d28094 : (x 13 13).toNat = 0 := by
        have r28095 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28096 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e28097 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b28098 := hb (x 11 3)
        have b28099 := hb (x 12 2)
        have b28100 := hb (x 13 13)
        have b28101 := hb (x 14 12)
        clear * - r28095 e28096 e28097 b28098 b28099 b28100 b28101 d28078 d28074
        omega
      have d28102 : (x 13 2 && x 13 13).toNat = 0 := by
        have r28103 := hand2 (x 13 2) (x 13 13)
        have b28104 := hb (x 13 13)
        have b28105 := hb (x 13 2 && x 13 13)
        clear * - r28103 b28104 b28105 d28094
        omega
      have d28106 : (x 13 3 && x 13 13).toNat = 0 := by
        have r28107 := hand2 (x 13 3) (x 13 13)
        have b28108 := hb (x 13 13)
        have b28109 := hb (x 13 3 && x 13 13)
        clear * - r28107 b28108 b28109 d28094
        omega
      have d28110 : (x 12 1 && x 12 14).toNat = 1 := by
        have r28111 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b28112 := hb (x 11 2)
        have b28113 := hb (x 13 13)
        have b28114 := hb (x 12 1 && x 12 14)
        clear * - r28111 b28112 b28113 b28114 d28094 d27922
        omega
      have d28115 : (x 12 1).toNat = 1 := by
        have r28116 := hand1 (x 12 1) (x 12 14)
        have b28117 := hb (x 12 1)
        have b28118 := hb (x 12 1 && x 12 14)
        clear * - r28116 b28117 b28118 d28110
        omega
      have d28119 : (x 13 14).toNat = 0 := by
        have r28120 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b28121 := hb (x 12 1)
        have b28122 := hb (x 13 14)
        clear * - r28120 b28121 b28122 d28115
        omega
      have d28123 : (x 13 1 && x 13 14).toNat = 0 := by
        have r28124 := hand2 (x 13 1) (x 13 14)
        have b28125 := hb (x 13 14)
        have b28126 := hb (x 13 1 && x 13 14)
        clear * - r28124 b28125 b28126 d28119
        omega
      have d28127 : (x 13 2).toNat = 0 := by
        have r28128 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
        have b28129 := hb (x 13 2)
        have b28130 := hb (x 13 14)
        clear * - r28128 b28129 b28130 d28119
        omega
      have d28131 : (x 12 2).toNat = 0 := by
        have r28132 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28133 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e28134 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b28135 := hb (x 11 3)
        have b28136 := hb (x 12 2)
        have b28137 := hb (x 13 13)
        have b28138 := hb (x 14 12)
        clear * - r28132 e28133 e28134 b28135 b28136 b28137 b28138 d28078 d28094 d28074
        omega
      have d28139 : (x 14 13).toNat = 1 := by
        have r28140 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b28141 := hb (x 12 2)
        have b28142 := hb (x 14 13)
        have b28143 := hb (x 13 1 && x 13 14)
        clear * - r28140 b28141 b28142 b28143 d28123 d28131
        omega
      have d28144 : (x 15 12).toNat = 0 := by
        have r28145 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28146 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e28147 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b28148 := hb (x 12 3)
        have b28149 := hb (x 13 2)
        have b28150 := hb (x 14 13)
        have b28151 := hb (x 15 12)
        clear * - r28145 e28146 e28147 b28148 b28149 b28150 b28151 d28139 d28127
        omega
      have d28152 : (x 12 3).toNat = 0 := by
        have r28153 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28154 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e28155 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b28156 := hb (x 12 3)
        have b28157 := hb (x 13 2)
        have b28158 := hb (x 14 13)
        have b28159 := hb (x 15 12)
        clear * - r28153 e28154 e28155 b28156 b28157 b28158 b28159 d28144 d28139 d28127
        omega
      have d28160 : (x 12 3 && x 12 14).toNat = 0 := by
        have r28161 := hand1 (x 12 3) (x 12 14)
        have b28162 := hb (x 12 3)
        have b28163 := hb (x 12 3 && x 12 14)
        clear * - r28161 b28162 b28163 d28152
        omega
      have d28164 : (x 15 11).toNat = 1 := by
        have r28165 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b28166 := hb (x 11 4)
        have b28167 := hb (x 15 11)
        have b28168 := hb (x 14 1 && x 14 12)
        have b28169 := hb (x 13 2 && x 13 13)
        have b28170 := hb (x 12 3 && x 12 14)
        clear * - r28165 b28166 b28167 b28168 b28169 b28170 d28086 d28102 d28160 d28051
        omega
      have d28171 : (x 15 3).toNat = 1 := by
        have r28172 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
        have b28173 := hb (x 15 3)
        have b28174 := hb (x 15 11)
        clear * - r28172 b28173 b28174 d28164
        omega
      have d28175 : (x 18 12).toNat = 0 := by
        have r28176 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28177 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
        have e28178 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
        have b28179 := hb (x 15 3)
        have b28180 := hb (x 16 2)
        have b28181 := hb (x 17 13)
        have b28182 := hb (x 18 12)
        clear * - r28176 e28177 e28178 b28179 b28180 b28181 b28182 d28171
        omega
      have d28183 : (x 17 13).toNat = 0 := by
        have r28184 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28185 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
        have e28186 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
        have b28187 := hb (x 15 3)
        have b28188 := hb (x 16 2)
        have b28189 := hb (x 17 13)
        have b28190 := hb (x 18 12)
        clear * - r28184 e28185 e28186 b28187 b28188 b28189 b28190 d28175 d28171
        omega
      have d28191 : (x 16 1 && x 16 14).toNat = 1 := by
        have r28192 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b28193 := hb (x 15 2)
        have b28194 := hb (x 17 13)
        have b28195 := hb (x 16 1 && x 16 14)
        clear * - r28192 b28193 b28194 b28195 d28183 d28035
        omega
      have d28196 : (x 16 14).toNat = 1 := by
        have r28197 := hand2 (x 16 1) (x 16 14)
        have b28198 := hb (x 16 14)
        have b28199 := hb (x 16 1 && x 16 14)
        clear * - r28197 b28198 b28199 d28191
        omega
      have d28200 : (x 15 1).toNat = 0 := by
        have r28201 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b28202 := hb (x 15 1)
        have b28203 := hb (x 16 14)
        clear * - r28201 b28202 b28203 d28196
        omega
      have d28204 : (x 15 1 && x 15 11).toNat = 0 := by
        have r28205 := hand1 (x 15 1) (x 15 11)
        have b28206 := hb (x 15 1)
        have b28207 := hb (x 15 1 && x 15 11)
        clear * - r28205 b28206 b28207 d28200
        omega
      have d28208 : (x 16 2).toNat = 0 := by
        have r28209 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28210 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
        have e28211 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
        have b28212 := hb (x 15 3)
        have b28213 := hb (x 16 2)
        have b28214 := hb (x 17 13)
        have b28215 := hb (x 18 12)
        clear * - r28209 e28210 e28211 b28212 b28213 b28214 b28215 d28175 d28183 d28171
        omega
      have d28216 : (x 16 10).toNat = 0 := by
        have r28217 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
        have b28218 := hb (x 16 2)
        have b28219 := hb (x 16 10)
        clear * - r28217 b28218 b28219 d28208
        omega
      have r28220 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := by have q := hcov10 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28221 := hb (x 11 5)
      have b28222 := hb (x 16 10)
      have b28223 := hb (x 15 1 && x 15 11)
      have b28224 := hb (x 14 2 && x 14 12)
      have b28225 := hb (x 13 3 && x 13 13)
      have b28226 := hb (x 12 4 && x 12 14)
      linarith only [r28220, b28221, b28222, b28223, b28224, b28225, b28226, d28216, d28204, d28090, d28106, d27988, d28000]
    · have f28227 : (x 0 3).toNat = 1 := by rw [h27617]; rfl
      have d28228 : (x 3 12).toNat = 0 := by
        have r28229 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28230 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e28231 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b28232 := hb (x 0 3)
        have b28233 := hb (x 1 2)
        have b28234 := hb (x 2 13)
        have b28235 := hb (x 3 12)
        clear * - r28229 e28230 e28231 b28232 b28233 b28234 b28235 d27496 f28227
        omega
      have d28236 : (x 3 1 && x 3 12).toNat = 0 := by
        have r28237 := hand2 (x 3 1) (x 3 12)
        have b28238 := hb (x 3 12)
        have b28239 := hb (x 3 1 && x 3 12)
        clear * - r28237 b28238 b28239 d28228
        omega
      have d28240 : (x 3 3 && x 3 12).toNat = 0 := by
        have r28241 := hand2 (x 3 3) (x 3 12)
        have b28242 := hb (x 3 12)
        have b28243 := hb (x 3 3 && x 3 12)
        clear * - r28241 b28242 b28243 d28228
        omega
      have d28244 : (x 3 4).toNat = 0 := by
        have r28245 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
        have b28246 := hb (x 3 4)
        have b28247 := hb (x 3 12)
        clear * - r28245 b28246 b28247 d28228
        omega
      have d28248 : (x 2 13).toNat = 0 := by
        have r28249 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28250 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e28251 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b28252 := hb (x 0 3)
        have b28253 := hb (x 1 2)
        have b28254 := hb (x 2 13)
        have b28255 := hb (x 3 12)
        clear * - r28249 e28250 e28251 b28252 b28253 b28254 b28255 d28228 d27496 f28227
        omega
      have d28256 : (x 2 2 && x 2 13).toNat = 0 := by
        have r28257 := hand2 (x 2 2) (x 2 13)
        have b28258 := hb (x 2 13)
        have b28259 := hb (x 2 2 && x 2 13)
        clear * - r28257 b28258 b28259 d28248
        omega
      have d28260 : (x 2 3 && x 2 13).toNat = 0 := by
        have r28261 := hand2 (x 2 3) (x 2 13)
        have b28262 := hb (x 2 13)
        have b28263 := hb (x 2 3 && x 2 13)
        clear * - r28261 b28262 b28263 d28248
        omega
      have d28264 : (x 2 5).toNat = 0 := by
        have r28265 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
        have b28266 := hb (x 2 5)
        have b28267 := hb (x 2 13)
        clear * - r28265 b28266 b28267 d28248
        omega
      have d28268 : (x 4 11).toNat = 1 := by
        have r28269 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b28270 := hb (x 0 4)
        have b28271 := hb (x 4 11)
        have b28272 := hb (x 3 1 && x 3 12)
        have b28273 := hb (x 2 2 && x 2 13)
        have b28274 := hb (x 1 3 && x 1 14)
        clear * - r28269 b28270 b28271 b28272 b28273 b28274 d28236 d28256 d27484 g6
        omega
      have d28275 : (x 4 3).toNat = 1 := by
        have r28276 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
        have b28277 := hb (x 4 3)
        have b28278 := hb (x 4 11)
        clear * - r28276 b28277 b28278 d28268
        omega
      have d28279 : (x 7 12).toNat = 0 := by
        have r28280 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28281 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e28282 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b28283 := hb (x 4 3)
        have b28284 := hb (x 5 2)
        have b28285 := hb (x 6 13)
        have b28286 := hb (x 7 12)
        clear * - r28280 e28281 e28282 b28283 b28284 b28285 b28286 d28275
        omega
      have d28287 : (x 7 4).toNat = 0 := by
        have r28288 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
        have b28289 := hb (x 7 4)
        have b28290 := hb (x 7 12)
        clear * - r28288 b28289 b28290 d28279
        omega
      have d28291 : (x 7 4 && x 7 13).toNat = 0 := by
        have r28292 := hand1 (x 7 4) (x 7 13)
        have b28293 := hb (x 7 4)
        have b28294 := hb (x 7 4 && x 7 13)
        clear * - r28292 b28293 b28294 d28287
        omega
      have d28295 : (x 6 13).toNat = 0 := by
        have r28296 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28297 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e28298 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b28299 := hb (x 4 3)
        have b28300 := hb (x 5 2)
        have b28301 := hb (x 6 13)
        have b28302 := hb (x 7 12)
        clear * - r28296 e28297 e28298 b28299 b28300 b28301 b28302 d28279 d28275
        omega
      have d28303 : (x 6 5).toNat = 0 := by
        have r28304 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
        have b28305 := hb (x 6 5)
        have b28306 := hb (x 6 13)
        clear * - r28304 b28305 b28306 d28295
        omega
      have d28307 : (x 6 5 && x 6 14).toNat = 0 := by
        have r28308 := hand1 (x 6 5) (x 6 14)
        have b28309 := hb (x 6 5)
        have b28310 := hb (x 6 5 && x 6 14)
        clear * - r28308 b28309 b28310 d28303
        omega
      have d28311 : (x 5 2).toNat = 0 := by
        have r28312 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28313 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e28314 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b28315 := hb (x 4 3)
        have b28316 := hb (x 5 2)
        have b28317 := hb (x 6 13)
        have b28318 := hb (x 7 12)
        clear * - r28312 e28313 e28314 b28315 b28316 b28317 b28318 d28279 d28295 d28275
        omega
      have d28319 : (x 5 10).toNat = 0 := by
        have r28320 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
        have b28321 := hb (x 5 2)
        have b28322 := hb (x 5 10)
        clear * - r28320 b28321 b28322 d28311
        omega
      have d28323 : (x 5 1 && x 5 10).toNat = 0 := by
        have r28324 := hand2 (x 5 1) (x 5 10)
        have b28325 := hb (x 5 10)
        have b28326 := hb (x 5 1 && x 5 10)
        clear * - r28324 b28325 b28326 d28319
        omega
      have d28327 : (x 7 8).toNat = 0 := by
        have r28328 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28329 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e28330 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e28331 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e28332 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e28333 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e28334 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b28335 := hb (x 0 7)
        have b28336 := hb (x 1 6)
        have b28337 := hb (x 2 5)
        have b28338 := hb (x 3 4)
        have b28339 := hb (x 4 11)
        have b28340 := hb (x 5 10)
        have b28341 := hb (x 6 9)
        have b28342 := hb (x 7 8)
        clear * - r28328 e28329 e28330 e28331 e28332 e28333 e28334 b28335 b28336 b28337 b28338 b28339 b28340 b28341 b28342 d28319 d28268 d28244 d28264 d27492
        omega
      have d28343 : (x 6 9).toNat = 0 := by
        have r28344 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28345 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e28346 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e28347 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e28348 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e28349 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e28350 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b28351 := hb (x 0 7)
        have b28352 := hb (x 1 6)
        have b28353 := hb (x 2 5)
        have b28354 := hb (x 3 4)
        have b28355 := hb (x 4 11)
        have b28356 := hb (x 5 10)
        have b28357 := hb (x 6 9)
        have b28358 := hb (x 7 8)
        clear * - r28344 e28345 e28346 e28347 e28348 e28349 e28350 b28351 b28352 b28353 b28354 b28355 b28356 b28357 b28358 d28327 d28319 d28268 d28244 d28264 d27492
        omega
      cases h28359 : x 0 5
      · have f28360 : (x 0 5).toNat = 0 := by rw [h28359]; rfl
        have d28361 : (x 4 1 && x 4 11).toNat = 1 := by
          have r28362 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28363 := hb (x 0 5)
          have b28364 := hb (x 5 10)
          have b28365 := hb (x 4 1 && x 4 11)
          have b28366 := hb (x 3 2 && x 3 12)
          have b28367 := hb (x 2 3 && x 2 13)
          have b28368 := hb (x 1 4 && x 1 14)
          clear * - r28362 b28363 b28364 b28365 b28366 b28367 b28368 d28319 d27537 d28260 d27488 f28360
          omega
        have d28369 : (x 4 1).toNat = 1 := by
          have r28370 := hand1 (x 4 1) (x 4 11)
          have b28371 := hb (x 4 1)
          have b28372 := hb (x 4 1 && x 4 11)
          clear * - r28370 b28371 b28372 d28361
          omega
        have d28373 : (x 5 14).toNat = 0 := by
          have r28374 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28375 := hb (x 4 1)
          have b28376 := hb (x 5 14)
          clear * - r28374 b28375 b28376 d28369
          omega
        have d28377 : (x 5 1 && x 5 14).toNat = 0 := by
          have r28378 := hand2 (x 5 1) (x 5 14)
          have b28379 := hb (x 5 14)
          have b28380 := hb (x 5 1 && x 5 14)
          clear * - r28378 b28379 b28380 d28373
          omega
        have d28381 : (x 4 2).toNat = 1 := by
          have r28382 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28383 := hb (x 4 2)
          have b28384 := hb (x 6 13)
          have b28385 := hb (x 5 1 && x 5 14)
          clear * - r28382 b28383 b28384 b28385 d28295 d28377
          omega
        have d28386 : (x 4 14).toNat = 1 := by
          have r28387 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
          have b28388 := hb (x 4 2)
          have b28389 := hb (x 4 14)
          clear * - r28387 b28388 b28389 d28381
          omega
        have d28390 : (x 3 1).toNat = 0 := by
          have r28391 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28392 := hb (x 3 1)
          have b28393 := hb (x 4 14)
          clear * - r28391 b28392 b28393 d28386
          omega
        have d28394 : (x 3 1 && x 3 11).toNat = 0 := by
          have r28395 := hand1 (x 3 1) (x 3 11)
          have b28396 := hb (x 3 1)
          have b28397 := hb (x 3 1 && x 3 11)
          clear * - r28395 b28396 b28397 d28390
          omega
        have d28398 : (x 3 13).toNat = 0 := by
          have r28399 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
          have b28400 := hb (x 3 1)
          have b28401 := hb (x 3 13)
          clear * - r28399 b28400 b28401 d28390
          omega
        have d28402 : (x 3 3 && x 3 13).toNat = 0 := by
          have r28403 := hand2 (x 3 3) (x 3 13)
          have b28404 := hb (x 3 13)
          have b28405 := hb (x 3 3 && x 3 13)
          clear * - r28403 b28404 b28405 d28398
          omega
        have d28406 : (x 3 7 && x 3 13).toNat = 0 := by
          have r28407 := hand2 (x 3 7) (x 3 13)
          have b28408 := hb (x 3 13)
          have b28409 := hb (x 3 7 && x 3 13)
          clear * - r28407 b28408 b28409 d28398
          omega
        have d28410 : (x 3 5).toNat = 0 := by
          have r28411 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
          have b28412 := hb (x 3 5)
          have b28413 := hb (x 3 13)
          clear * - r28411 b28412 b28413 d28398
          omega
        have d28414 : (x 3 5 && x 3 11).toNat = 0 := by
          have r28415 := hand1 (x 3 5) (x 3 11)
          have b28416 := hb (x 3 5)
          have b28417 := hb (x 3 5 && x 3 11)
          clear * - r28415 b28416 b28417 d28410
          omega
        have d28418 : (x 3 5 && x 3 9).toNat = 0 := by
          have r28419 := hand1 (x 3 5) (x 3 9)
          have b28420 := hb (x 3 5)
          have b28421 := hb (x 3 5 && x 3 9)
          clear * - r28419 b28420 b28421 d28410
          omega
        have d28422 : (x 2 1 && x 2 14).toNat = 1 := by
          have r28423 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28424 := hb (x 1 2)
          have b28425 := hb (x 3 13)
          have b28426 := hb (x 2 1 && x 2 14)
          clear * - r28423 b28424 b28425 b28426 d28398 d27496
          omega
        have d28427 : (x 2 14).toNat = 1 := by
          have r28428 := hand2 (x 2 1) (x 2 14)
          have b28429 := hb (x 2 14)
          have b28430 := hb (x 2 1 && x 2 14)
          clear * - r28428 b28429 b28430 d28422
          omega
        have d28431 : (x 1 1).toNat = 0 := by
          have r28432 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28433 := hb (x 1 1)
          have b28434 := hb (x 2 14)
          clear * - r28432 b28433 b28434 d28427
          omega
        have d28435 : (x 1 1 && x 1 11).toNat = 0 := by
          have r28436 := hand1 (x 1 1) (x 1 11)
          have b28437 := hb (x 1 1)
          have b28438 := hb (x 1 1 && x 1 11)
          clear * - r28436 b28437 b28438 d28431
          omega
        have d28439 : (x 1 1 && x 1 7).toNat = 0 := by
          have r28440 := hand1 (x 1 1) (x 1 7)
          have b28441 := hb (x 1 1)
          have b28442 := hb (x 1 1 && x 1 7)
          clear * - r28440 b28441 b28442 d28431
          omega
        have d28443 : (x 3 9).toNat = 0 := by
          have r28444 : (x 3 9).toNat ≤ (x 3 1).toNat := himp _ _ (hp9 3)
          have b28445 := hb (x 3 1)
          have b28446 := hb (x 3 9)
          clear * - r28444 b28445 b28446 d28390
          omega
        have d28447 : (x 6 12).toNat = 0 := by
          have r28448 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28449 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e28450 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b28451 := hb (x 3 3)
          have b28452 := hb (x 4 2)
          have b28453 := hb (x 5 13)
          have b28454 := hb (x 6 12)
          clear * - r28448 e28449 e28450 b28451 b28452 b28453 b28454 d28381
          omega
        have d28455 : (x 6 2 && x 6 12).toNat = 0 := by
          have r28456 := hand2 (x 6 2) (x 6 12)
          have b28457 := hb (x 6 12)
          have b28458 := hb (x 6 2 && x 6 12)
          clear * - r28456 b28457 b28458 d28447
          omega
        have d28459 : (x 6 4).toNat = 0 := by
          have r28460 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
          have b28461 := hb (x 6 4)
          have b28462 := hb (x 6 12)
          clear * - r28460 b28461 b28462 d28447
          omega
        have d28463 : (x 6 4 && x 6 14).toNat = 0 := by
          have r28464 := hand1 (x 6 4) (x 6 14)
          have b28465 := hb (x 6 4)
          have b28466 := hb (x 6 4 && x 6 14)
          clear * - r28464 b28465 b28466 d28459
          omega
        have d28467 : (x 6 4 && x 6 10).toNat = 0 := by
          have r28468 := hand1 (x 6 4) (x 6 10)
          have b28469 := hb (x 6 4)
          have b28470 := hb (x 6 4 && x 6 10)
          clear * - r28468 b28469 b28470 d28459
          omega
        have d28471 : (x 5 13).toNat = 0 := by
          have r28472 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28473 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e28474 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b28475 := hb (x 3 3)
          have b28476 := hb (x 4 2)
          have b28477 := hb (x 5 13)
          have b28478 := hb (x 6 12)
          clear * - r28472 e28473 e28474 b28475 b28476 b28477 b28478 d28447 d28381
          omega
        have d28479 : (x 5 3 && x 5 13).toNat = 0 := by
          have r28480 := hand2 (x 5 3) (x 5 13)
          have b28481 := hb (x 5 13)
          have b28482 := hb (x 5 3 && x 5 13)
          clear * - r28480 b28481 b28482 d28471
          omega
        have d28483 : (x 5 5).toNat = 0 := by
          have r28484 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
          have b28485 := hb (x 5 5)
          have b28486 := hb (x 5 13)
          clear * - r28484 b28485 b28486 d28471
          omega
        have d28487 : (x 5 5 && x 5 11).toNat = 0 := by
          have r28488 := hand1 (x 5 5) (x 5 11)
          have b28489 := hb (x 5 5)
          have b28490 := hb (x 5 5 && x 5 11)
          clear * - r28488 b28489 b28490 d28483
          omega
        have d28491 : (x 3 3).toNat = 0 := by
          have r28492 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28493 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e28494 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b28495 := hb (x 3 3)
          have b28496 := hb (x 4 2)
          have b28497 := hb (x 5 13)
          have b28498 := hb (x 6 12)
          clear * - r28492 e28493 e28494 b28495 b28496 b28497 b28498 d28447 d28471 d28381
          omega
        have d28499 : (x 3 11).toNat = 0 := by
          have r28500 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
          have b28501 := hb (x 3 3)
          have b28502 := hb (x 3 11)
          clear * - r28500 b28501 b28502 d28491
          omega
        have d28503 : (x 4 10).toNat = 1 := by
          have r28504 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b28505 := hb (x (-1) 5)
          have b28506 := hb (x 4 10)
          have b28507 := hb (x 3 1 && x 3 11)
          have b28508 := hb (x 2 2 && x 2 12)
          have b28509 := hb (x 1 3 && x 1 13)
          have b28510 := hb (x 0 4 && x 0 14)
          clear * - r28504 b28505 b28506 b28507 b28508 b28509 b28510 d28394 g38 g39 d27178 g3
          omega
        have d28511 : (x 6 8).toNat = 0 := by
          have r28512 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28513 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e28514 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e28515 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e28516 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e28517 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e28518 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b28519 := hb (x (-1) 7)
          have b28520 := hb (x 0 6)
          have b28521 := hb (x 1 5)
          have b28522 := hb (x 2 4)
          have b28523 := hb (x 3 11)
          have b28524 := hb (x 4 10)
          have b28525 := hb (x 5 9)
          have b28526 := hb (x 6 8)
          clear * - r28512 e28513 e28514 e28515 e28516 e28517 e28518 b28519 b28520 b28521 b28522 b28523 b28524 b28525 b28526 d28503 d28499 g12 g9
          omega
        have d28527 : (x 6 2 && x 6 8).toNat = 0 := by
          have r28528 := hand2 (x 6 2) (x 6 8)
          have b28529 := hb (x 6 8)
          have b28530 := hb (x 6 2 && x 6 8)
          clear * - r28528 b28529 b28530 d28511
          omega
        have d28531 : (x 5 9).toNat = 0 := by
          have r28532 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28533 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e28534 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e28535 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e28536 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e28537 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e28538 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b28539 := hb (x (-1) 7)
          have b28540 := hb (x 0 6)
          have b28541 := hb (x 1 5)
          have b28542 := hb (x 2 4)
          have b28543 := hb (x 3 11)
          have b28544 := hb (x 4 10)
          have b28545 := hb (x 5 9)
          have b28546 := hb (x 6 8)
          clear * - r28532 e28533 e28534 e28535 e28536 e28537 e28538 b28539 b28540 b28541 b28542 b28543 b28544 b28545 b28546 d28511 d28503 d28499 g12 g9
          omega
        have d28547 : (x 5 3 && x 5 9).toNat = 0 := by
          have r28548 := hand2 (x 5 3) (x 5 9)
          have b28549 := hb (x 5 9)
          have b28550 := hb (x 5 3 && x 5 9)
          clear * - r28548 b28549 b28550 d28531
          omega
        have d28551 : (x 0 6).toNat = 0 := by
          have r28552 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28553 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e28554 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e28555 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e28556 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e28557 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e28558 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have b28559 := hb (x (-1) 7)
          have b28560 := hb (x 0 6)
          have b28561 := hb (x 1 5)
          have b28562 := hb (x 2 4)
          have b28563 := hb (x 3 11)
          have b28564 := hb (x 4 10)
          have b28565 := hb (x 5 9)
          have b28566 := hb (x 6 8)
          clear * - r28552 e28553 e28554 e28555 e28556 e28557 e28558 b28559 b28560 b28561 b28562 b28563 b28564 b28565 b28566 d28511 d28531 d28503 d28499 g12 g9
          omega
        have d28567 : (x 0 2 && x 0 6).toNat = 0 := by
          have r28568 := hand2 (x 0 2) (x 0 6)
          have b28569 := hb (x 0 6)
          have b28570 := hb (x 0 2 && x 0 6)
          clear * - r28568 b28569 b28570 d28551
          omega
        cases h28571 : x 0 8
        · have f28572 : (x 0 8).toNat = 0 := by rw [h28571]; rfl
          have d28573 : (x 0 8 && x 0 14).toNat = 0 := by
            have r28574 := hand1 (x 0 8) (x 0 14)
            have b28575 := hb (x 0 8)
            have b28576 := hb (x 0 8 && x 0 14)
            clear * - r28574 b28575 b28576 f28572
            omega
          have d28577 : (x 0 2 && x 0 8).toNat = 0 := by
            have r28578 := hand2 (x 0 2) (x 0 8)
            have b28579 := hb (x 0 8)
            have b28580 := hb (x 0 2 && x 0 8)
            clear * - r28578 b28579 b28580 f28572
            omega
          have r28581 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28582 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28583 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
          have e28584 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
          have e28585 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
          have e28586 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
          have e28587 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
          have e28588 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
          have r28589 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28590 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e28591 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e28592 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e28593 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e28594 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e28595 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have r28596 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28597 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
          have e28598 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
          have e28599 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
          have e28600 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
          have e28601 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
          have e28602 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
          have r28603 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28604 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e28605 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e28606 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e28607 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e28608 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e28609 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have r28610 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28611 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e28612 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have r28613 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28614 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e28615 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have r28616 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28617 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e28618 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have r28619 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28620 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e28621 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have r28622 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28623 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
          have e28624 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
          have r28625 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28626 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28627 : 1 ≤ (x 10 6).toNat + (x 9 1 && x 9 7).toNat + (x 8 2 && x 8 8).toNat + (x 7 3 && x 7 9).toNat + (x 6 4 && x 6 10).toNat + (x 5 5 && x 5 11).toNat + (x 4 6 && x 4 12).toNat + (x 3 7 && x 3 13).toNat + (x 2 8 && x 2 14).toNat + (x 1 9).toNat := by have q := hcov6 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28628 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28629 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28630 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28631 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := by have q := hcov10 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28632 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28633 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28634 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
          have r28635 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
          have r28636 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
          have r28637 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
          have r28638 := hand2 (x (-6) 8) (x (-6) 12)
          have r28639 := hand2 (x (-7) 9) (x (-7) 13)
          have r28640 := hand1 (x (-6) 8) (x (-6) 14)
          have r28641 := hand2 (x 7 1) (x 7 7)
          have r28642 := hand1 (x 4 4) (x 4 10)
          have r28643 := hand2 (x 9 1) (x 9 7)
          have r28644 := hand2 (x 8 2) (x 8 8)
          have r28645 := hand2 (x 7 3) (x 7 9)
          have r28646 := hand1 (x 4 6) (x 4 12)
          have r28647 := hand2 (x (-7) 1) (x (-7) 11)
          have r28648 := hand1 (x (-8) 2) (x (-8) 12)
          have r28649 := hand1 (x (-9) 3) (x (-9) 13)
          have r28650 := hand1 (x (-10) 4) (x (-10) 14)
          have r28651 := hand2 (x 0 2) (x 0 12)
          have r28652 := hand2 (x 5 1) (x 5 11)
          have r28653 := hand2 (x 4 2) (x 4 12)
          have r28654 := hand2 (x 7 1) (x 7 11)
          have r28655 := hand1 (x 4 4) (x 4 14)
          have r28656 := hand1 (x 13 1) (x 13 11)
          have r28657 := hand1 (x 12 2) (x 12 12)
          have r28658 := hand1 (x 11 3) (x 11 13)
          have r28659 := hand1 (x 10 4) (x 10 14)
          have r28660 := hand1 (x (-2) 2) (x (-2) 13)
          have r28661 := hand1 (x (-3) 3) (x (-3) 14)
          linarith only [r28581, r28582, e28583, e28584, e28585, e28586, e28587, e28588, r28589, e28590, e28591, e28592, e28593, e28594, e28595, r28596, e28597, e28598, e28599, e28600, e28601, e28602, r28603, e28604, e28605, e28606, e28607, e28608, e28609, r28610, e28611, e28612, r28613, e28614, e28615, r28616, e28617, e28618, r28619, e28620, e28621, r28622, e28623, e28624, r28625, r28626, r28627, r28628, r28629, r28630, r28631, r28632, r28633, r28634, r28635, r28636, r28637, r28638, r28639, r28640, r28641, r28642, r28643, r28644, r28645, r28646, r28647, r28648, r28649, r28650, r28651, r28652, r28653, r28654, r28655, r28656, r28657, r28658, r28659, r28660, r28661, g1, g4, g5, g7, g8, g9, g10, g11, g12, g13, d28410, d28499, d28398, d28503, d28483, d28531, d28459, d28511, d28567, g14, g15, g16, g17, g18, d28439, d28577, g20, g21, g22, g23, g24, d28527, d28547, d28414, g25, g26, d28573, d28467, d28487, d28406, g27, d28435, g36, g37, d28402, g40, d28455, d28479, g41]
        · have f28789 : (x 0 8).toNat = 1 := by rw [h28571]; rfl
          have d28790 : (x (-2) 10).toNat = 0 := by
            have r28791 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28792 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
            have e28793 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
            have e28794 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
            have e28795 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
            have e28796 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
            have e28797 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
            have b28798 := hb (x (-7) 7)
            have b28799 := hb (x (-6) 6)
            have b28800 := hb (x (-5) 5)
            have b28801 := hb (x (-4) 4)
            have b28802 := hb (x (-3) 11)
            have b28803 := hb (x (-2) 10)
            have b28804 := hb (x (-1) 9)
            have b28805 := hb (x 0 8)
            clear * - r28791 e28792 e28793 e28794 e28795 e28796 e28797 b28798 b28799 b28800 b28801 b28802 b28803 b28804 b28805 f28789 g4
            omega
          have d28806 : (x (-3) 11).toNat = 0 := by
            have r28807 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28808 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
            have e28809 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
            have e28810 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
            have e28811 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
            have e28812 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
            have e28813 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
            have b28814 := hb (x (-7) 7)
            have b28815 := hb (x (-6) 6)
            have b28816 := hb (x (-5) 5)
            have b28817 := hb (x (-4) 4)
            have b28818 := hb (x (-3) 11)
            have b28819 := hb (x (-2) 10)
            have b28820 := hb (x (-1) 9)
            have b28821 := hb (x 0 8)
            clear * - r28807 e28808 e28809 e28810 e28811 e28812 e28813 b28814 b28815 b28816 b28817 b28818 b28819 b28820 b28821 f28789 g4 d28790
            omega
          have d28822 : (x (-4) 4).toNat = 0 := by
            have r28823 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e28824 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
            have e28825 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
            have e28826 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
            have e28827 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
            have e28828 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
            have e28829 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
            have b28830 := hb (x (-7) 7)
            have b28831 := hb (x (-6) 6)
            have b28832 := hb (x (-5) 5)
            have b28833 := hb (x (-4) 4)
            have b28834 := hb (x (-3) 11)
            have b28835 := hb (x (-2) 10)
            have b28836 := hb (x (-1) 9)
            have b28837 := hb (x 0 8)
            clear * - r28823 e28824 e28825 e28826 e28827 e28828 e28829 b28830 b28831 b28832 b28833 b28834 b28835 b28836 b28837 f28789 g4 d28790 d28806
            omega
          have r28838 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28839 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e28840 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e28841 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e28842 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e28843 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e28844 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have r28845 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28846 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e28847 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e28848 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e28849 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e28850 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e28851 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have r28852 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28853 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
          have e28854 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
          have e28855 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
          have e28856 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
          have e28857 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
          have e28858 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
          have r28859 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28860 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e28861 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have r28862 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28863 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e28864 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have r28865 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28866 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e28867 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have r28868 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28869 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
          have e28870 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
          have r28871 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28872 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28873 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28874 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r28875 : (x 2 10).toNat ≤ (x 2 2).toNat := himp _ _ (hp10 2)
          have r28876 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
          have r28877 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
          have r28878 := hand2 (x 6 2) (x 6 6)
          have r28879 := hand2 (x 5 3) (x 5 7)
          have r28880 := hand2 (x 4 4) (x 4 8)
          have r28881 := hand1 (x 2 6) (x 2 10)
          have r28882 := hand2 (x 1 7) (x 1 11)
          have r28883 := hand2 (x 0 8) (x 0 12)
          have r28884 := hand2 (x 0 2) (x 0 12)
          have r28885 := hand2 (x 5 1) (x 5 11)
          have r28886 := hand2 (x 4 2) (x 4 12)
          have r28887 := hand2 (x 9 1) (x 9 11)
          have r28888 := hand2 (x 8 2) (x 8 12)
          have r28889 := hand2 (x 7 3) (x 7 13)
          have r28890 := hand1 (x (-2) 2) (x (-2) 13)
          have r28891 := hand1 (x (-3) 3) (x (-3) 14)
          linarith only [r28838, e28839, e28840, e28841, e28842, e28843, e28844, r28845, e28846, e28847, e28848, e28849, e28850, e28851, r28852, e28853, e28854, e28855, e28856, e28857, e28858, r28859, e28860, e28861, r28862, e28863, e28864, r28865, e28866, e28867, r28868, e28869, e28870, r28871, r28872, r28873, r28874, r28875, r28876, r28877, r28878, r28879, r28880, r28881, r28882, r28883, r28884, r28885, r28886, r28887, r28888, r28889, r28890, r28891, d28822, g1, d28806, d28790, g3, g5, g6, g7, g9, d28410, d28443, d28398, d28483, d28418, g19, d28435, g36, g37, d28402, g40, d28463, g41]
      · have f28958 : (x 0 5).toNat = 1 := by rw [h28359]; rfl
        have d28959 : (x 0 13).toNat = 1 := by
          have r28960 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
          have b28961 := hb (x 0 5)
          have b28962 := hb (x 0 13)
          clear * - r28960 b28961 b28962 f28958
          omega
        have d28963 : (x 1 12).toNat = 0 := by
          have r28964 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28965 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e28966 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b28967 := hb (x (-2) 3)
          have b28968 := hb (x (-1) 2)
          have b28969 := hb (x 0 13)
          have b28970 := hb (x 1 12)
          clear * - r28964 e28965 e28966 b28967 b28968 b28969 b28970 d28959
          omega
        have d28971 : (x 1 3 && x 1 12).toNat = 0 := by
          have r28972 := hand2 (x 1 3) (x 1 12)
          have b28973 := hb (x 1 12)
          have b28974 := hb (x 1 3 && x 1 12)
          clear * - r28972 b28973 b28974 d28963
          omega
        have d28975 : (x 1 4).toNat = 0 := by
          have r28976 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
          have b28977 := hb (x 1 4)
          have b28978 := hb (x 1 12)
          clear * - r28976 b28977 b28978 d28963
          omega
        have d28979 : (x 5 8).toNat = 0 := by
          have r28980 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28981 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e28982 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e28983 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e28984 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e28985 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e28986 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b28987 := hb (x (-2) 7)
          have b28988 := hb (x (-1) 6)
          have b28989 := hb (x 0 5)
          have b28990 := hb (x 1 4)
          have b28991 := hb (x 2 11)
          have b28992 := hb (x 3 10)
          have b28993 := hb (x 4 9)
          have b28994 := hb (x 5 8)
          clear * - r28980 e28981 e28982 e28983 e28984 e28985 e28986 b28987 b28988 b28989 b28990 b28991 b28992 b28993 b28994 d27541 d28975 f28958
          omega
        have d28995 : (x 4 9).toNat = 0 := by
          have r28996 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e28997 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e28998 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e28999 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e29000 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e29001 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e29002 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b29003 := hb (x (-2) 7)
          have b29004 := hb (x (-1) 6)
          have b29005 := hb (x 0 5)
          have b29006 := hb (x 1 4)
          have b29007 := hb (x 2 11)
          have b29008 := hb (x 3 10)
          have b29009 := hb (x 4 9)
          have b29010 := hb (x 5 8)
          clear * - r28996 e28997 e28998 e28999 e29000 e29001 e29002 b29003 b29004 b29005 b29006 b29007 b29008 b29009 b29010 d28979 d27541 d28975 f28958
          omega
        have d29011 : (x 2 11).toNat = 0 := by
          have r29012 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29013 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e29014 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e29015 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e29016 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e29017 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e29018 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b29019 := hb (x (-2) 7)
          have b29020 := hb (x (-1) 6)
          have b29021 := hb (x 0 5)
          have b29022 := hb (x 1 4)
          have b29023 := hb (x 2 11)
          have b29024 := hb (x 3 10)
          have b29025 := hb (x 4 9)
          have b29026 := hb (x 5 8)
          clear * - r29012 e29013 e29014 e29015 e29016 e29017 e29018 b29019 b29020 b29021 b29022 b29023 b29024 b29025 b29026 d28979 d28995 d27541 d28975 f28958
          omega
        have d29027 : (x 2 2 && x 2 11).toNat = 0 := by
          have r29028 := hand2 (x 2 2) (x 2 11)
          have b29029 := hb (x 2 11)
          have b29030 := hb (x 2 2 && x 2 11)
          clear * - r29028 b29029 b29030 d29011
          omega
        have d29031 : (x (-2) 6).toNat = 1 := by
          have r29032 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29033 := hb (x (-2) 6)
          have b29034 := hb (x 4 9)
          have b29035 := hb (x 3 1 && x 3 10)
          have b29036 := hb (x 2 2 && x 2 11)
          have b29037 := hb (x 1 3 && x 1 12)
          have b29038 := hb (x 0 4 && x 0 13)
          have b29039 := hb (x (-1) 5 && x (-1) 14)
          clear * - r29032 b29033 b29034 b29035 b29036 b29037 b29038 b29039 d28995 d27545 d29027 d28971 d27182 g33
          omega
        have d29040 : (x (-2) 14).toNat = 1 := by
          have r29041 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
          have b29042 := hb (x (-2) 6)
          have b29043 := hb (x (-2) 14)
          clear * - r29041 b29042 b29043 d29031
          omega
        have d29044 : (x 4 8).toNat = 0 := by
          have r29045 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29046 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e29047 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e29048 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e29049 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e29050 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e29051 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b29052 := hb (x (-3) 7)
          have b29053 := hb (x (-2) 6)
          have b29054 := hb (x (-1) 5)
          have b29055 := hb (x 0 4)
          have b29056 := hb (x 1 11)
          have b29057 := hb (x 2 10)
          have b29058 := hb (x 3 9)
          have b29059 := hb (x 4 8)
          clear * - r29045 e29046 e29047 e29048 e29049 e29050 e29051 b29052 b29053 b29054 b29055 b29056 b29057 b29058 b29059 g6 g3 d29031
          omega
        have d29060 : (x 4 8 && x 4 12).toNat = 0 := by
          have r29061 := hand1 (x 4 8) (x 4 12)
          have b29062 := hb (x 4 8)
          have b29063 := hb (x 4 8 && x 4 12)
          clear * - r29061 b29062 b29063 d29044
          omega
        have d29064 : (x 4 4 && x 4 8).toNat = 0 := by
          have r29065 := hand2 (x 4 4) (x 4 8)
          have b29066 := hb (x 4 8)
          have b29067 := hb (x 4 4 && x 4 8)
          clear * - r29065 b29066 b29067 d29044
          omega
        have d29068 : (x 3 9).toNat = 0 := by
          have r29069 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29070 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e29071 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e29072 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e29073 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e29074 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e29075 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b29076 := hb (x (-3) 7)
          have b29077 := hb (x (-2) 6)
          have b29078 := hb (x (-1) 5)
          have b29079 := hb (x 0 4)
          have b29080 := hb (x 1 11)
          have b29081 := hb (x 2 10)
          have b29082 := hb (x 3 9)
          have b29083 := hb (x 4 8)
          clear * - r29069 e29070 e29071 e29072 e29073 e29074 e29075 b29076 b29077 b29078 b29079 b29080 b29081 b29082 b29083 d29044 g6 g3 d29031
          omega
        have d29084 : (x 3 9 && x 3 13).toNat = 0 := by
          have r29085 := hand1 (x 3 9) (x 3 13)
          have b29086 := hb (x 3 9)
          have b29087 := hb (x 3 9 && x 3 13)
          clear * - r29085 b29086 b29087 d29068
          omega
        have d29088 : (x 3 5 && x 3 9).toNat = 0 := by
          have r29089 := hand2 (x 3 5) (x 3 9)
          have b29090 := hb (x 3 9)
          have b29091 := hb (x 3 5 && x 3 9)
          clear * - r29089 b29090 b29091 d29068
          omega
        have d29092 : (x 2 10).toNat = 0 := by
          have r29093 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29094 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e29095 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e29096 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e29097 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e29098 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e29099 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b29100 := hb (x (-3) 7)
          have b29101 := hb (x (-2) 6)
          have b29102 := hb (x (-1) 5)
          have b29103 := hb (x 0 4)
          have b29104 := hb (x 1 11)
          have b29105 := hb (x 2 10)
          have b29106 := hb (x 3 9)
          have b29107 := hb (x 4 8)
          clear * - r29093 e29094 e29095 e29096 e29097 e29098 e29099 b29100 b29101 b29102 b29103 b29104 b29105 b29106 b29107 d29044 d29068 g6 g3 d29031
          omega
        have d29108 : (x 2 1 && x 2 10).toNat = 0 := by
          have r29109 := hand2 (x 2 1) (x 2 10)
          have b29110 := hb (x 2 10)
          have b29111 := hb (x 2 1 && x 2 10)
          clear * - r29109 b29110 b29111 d29092
          omega
        have d29112 : (x 0 3 && x 0 12).toNat = 1 := by
          have r29113 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29114 := hb (x (-3) 6)
          have b29115 := hb (x 3 9)
          have b29116 := hb (x 2 1 && x 2 10)
          have b29117 := hb (x 1 2 && x 1 11)
          have b29118 := hb (x 0 3 && x 0 12)
          have b29119 := hb (x (-1) 4 && x (-1) 13)
          have b29120 := hb (x (-2) 5 && x (-2) 14)
          clear * - r29113 b29114 b29115 b29116 b29117 b29118 b29119 b29120 d29068 d29108 d27500 g32 d27597 d27601
          omega
        have d29121 : (x 0 12).toNat = 1 := by
          have r29122 := hand2 (x 0 3) (x 0 12)
          have b29123 := hb (x 0 12)
          have b29124 := hb (x 0 3 && x 0 12)
          clear * - r29122 b29123 b29124 d29112
          omega
        have d29125 : (x (-2) 2).toNat = 0 := by
          have r29126 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29127 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e29128 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b29129 := hb (x (-3) 3)
          have b29130 := hb (x (-2) 2)
          have b29131 := hb (x (-1) 13)
          have b29132 := hb (x 0 12)
          clear * - r29126 e29127 e29128 b29129 b29130 b29131 b29132 d29121 g5
          omega
        have d29133 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
          have r29134 := hand1 (x (-2) 2) (x (-2) 13)
          have b29135 := hb (x (-2) 2)
          have b29136 := hb (x (-2) 2 && x (-2) 13)
          clear * - r29134 b29135 b29136 d29125
          omega
        have d29137 : (x (-2) 10).toNat = 0 := by
          have r29138 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
          have b29139 := hb (x (-2) 2)
          have b29140 := hb (x (-2) 10)
          clear * - r29138 b29139 b29140 d29125
          omega
        have d29141 : (x (-3) 3).toNat = 0 := by
          have r29142 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29143 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e29144 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b29145 := hb (x (-3) 3)
          have b29146 := hb (x (-2) 2)
          have b29147 := hb (x (-1) 13)
          have b29148 := hb (x 0 12)
          clear * - r29142 e29143 e29144 b29145 b29146 b29147 b29148 d29121 g5 d29125
          omega
        have d29149 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
          have r29150 := hand1 (x (-3) 3) (x (-3) 14)
          have b29151 := hb (x (-3) 3)
          have b29152 := hb (x (-3) 3 && x (-3) 14)
          clear * - r29150 b29151 b29152 d29141
          omega
        have d29153 : (x (-4) 4).toNat = 1 := by
          have r29154 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b29155 := hb (x (-4) 4)
          have b29156 := hb (x 0 11)
          have b29157 := hb (x (-1) 1 && x (-1) 12)
          have b29158 := hb (x (-2) 2 && x (-2) 13)
          have b29159 := hb (x (-3) 3 && x (-3) 14)
          clear * - r29154 b29155 b29156 b29157 b29158 b29159 g7 g41 d29133 d29149
          omega
        have d29160 : (x (-4) 12).toNat = 1 := by
          have r29161 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
          have b29162 := hb (x (-4) 4)
          have b29163 := hb (x (-4) 12)
          clear * - r29161 b29162 b29163 d29153
          omega
        have d29164 : (x (-5) 13).toNat = 0 := by
          have r29165 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29166 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e29167 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b29168 := hb (x (-7) 3)
          have b29169 := hb (x (-6) 2)
          have b29170 := hb (x (-5) 13)
          have b29171 := hb (x (-4) 12)
          clear * - r29165 e29166 e29167 b29168 b29169 b29170 b29171 d29160
          omega
        have d29172 : (x (-5) 5).toNat = 0 := by
          have r29173 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
          have b29174 := hb (x (-5) 5)
          have b29175 := hb (x (-5) 13)
          clear * - r29173 b29174 b29175 d29164
          omega
        have d29176 : (x (-6) 2).toNat = 0 := by
          have r29177 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29178 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e29179 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b29180 := hb (x (-7) 3)
          have b29181 := hb (x (-6) 2)
          have b29182 := hb (x (-5) 13)
          have b29183 := hb (x (-4) 12)
          clear * - r29177 e29178 e29179 b29180 b29181 b29182 b29183 d29160 d29164
          omega
        have d29184 : (x (-6) 10).toNat = 0 := by
          have r29185 : (x (-6) 10).toNat ≤ (x (-6) 2).toNat := himp _ _ (hp10 (-6))
          have b29186 := hb (x (-6) 2)
          have b29187 := hb (x (-6) 10)
          clear * - r29185 b29186 b29187 d29176
          omega
        have d29188 : (x (-7) 3).toNat = 0 := by
          have r29189 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := by have q := hd12 (-4); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29190 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
          have e29191 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
          have b29192 := hb (x (-7) 3)
          have b29193 := hb (x (-6) 2)
          have b29194 := hb (x (-5) 13)
          have b29195 := hb (x (-4) 12)
          clear * - r29189 e29190 e29191 b29192 b29193 b29194 b29195 d29160 d29164 d29176
          omega
        have d29196 : (x (-7) 11).toNat = 0 := by
          have r29197 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
          have b29198 := hb (x (-7) 3)
          have b29199 := hb (x (-7) 11)
          clear * - r29197 b29198 b29199 d29188
          omega
        have d29200 : (x (-7) 1 && x (-7) 11).toNat = 0 := by
          have r29201 := hand2 (x (-7) 1) (x (-7) 11)
          have b29202 := hb (x (-7) 11)
          have b29203 := hb (x (-7) 1 && x (-7) 11)
          clear * - r29201 b29202 b29203 d29196
          omega
        have d29204 : (x (-3) 11).toNat = 0 := by
          have r29205 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
          have b29206 := hb (x (-3) 3)
          have b29207 := hb (x (-3) 11)
          clear * - r29205 b29206 b29207 d29141
          omega
        have d29208 : (x 2 6 && x 2 10).toNat = 0 := by
          have r29209 := hand2 (x 2 6) (x 2 10)
          have b29210 := hb (x 2 10)
          have b29211 := hb (x 2 6 && x 2 10)
          clear * - r29209 b29210 b29211 d29092
          omega
        have d29212 : (x 1 11).toNat = 0 := by
          have r29213 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29214 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
          have e29215 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
          have e29216 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
          have e29217 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
          have e29218 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
          have e29219 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
          have b29220 := hb (x (-3) 7)
          have b29221 := hb (x (-2) 6)
          have b29222 := hb (x (-1) 5)
          have b29223 := hb (x 0 4)
          have b29224 := hb (x 1 11)
          have b29225 := hb (x 2 10)
          have b29226 := hb (x 3 9)
          have b29227 := hb (x 4 8)
          clear * - r29213 e29214 e29215 e29216 e29217 e29218 e29219 b29220 b29221 b29222 b29223 b29224 b29225 b29226 b29227 d29044 d29068 d29092 g6 g3 d29031
          omega
        have d29228 : (x 1 7 && x 1 11).toNat = 0 := by
          have r29229 := hand2 (x 1 7) (x 1 11)
          have b29230 := hb (x 1 11)
          have b29231 := hb (x 1 7 && x 1 11)
          clear * - r29229 b29230 b29231 d29212
          omega
        have d29232 : (x 0 8).toNat = 0 := by
          have r29233 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29234 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e29235 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e29236 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e29237 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e29238 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e29239 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b29240 := hb (x (-7) 7)
          have b29241 := hb (x (-6) 6)
          have b29242 := hb (x (-5) 5)
          have b29243 := hb (x (-4) 4)
          have b29244 := hb (x (-3) 11)
          have b29245 := hb (x (-2) 10)
          have b29246 := hb (x (-1) 9)
          have b29247 := hb (x 0 8)
          clear * - r29233 e29234 e29235 e29236 e29237 e29238 e29239 b29240 b29241 b29242 b29243 b29244 b29245 b29246 b29247 g4 d29137 d29204 d29153 d29172
          omega
        have d29248 : (x 0 8 && x 0 14).toNat = 0 := by
          have r29249 := hand1 (x 0 8) (x 0 14)
          have b29250 := hb (x 0 8)
          have b29251 := hb (x 0 8 && x 0 14)
          clear * - r29249 b29250 b29251 d29232
          omega
        have d29252 : (x 0 2 && x 0 8).toNat = 0 := by
          have r29253 := hand2 (x 0 2) (x 0 8)
          have b29254 := hb (x 0 8)
          have b29255 := hb (x 0 2 && x 0 8)
          clear * - r29253 b29254 b29255 d29232
          omega
        have d29256 : (x 0 8 && x 0 12).toNat = 0 := by
          have r29257 := hand1 (x 0 8) (x 0 12)
          have b29258 := hb (x 0 8)
          have b29259 := hb (x 0 8 && x 0 12)
          clear * - r29257 b29258 b29259 d29232
          omega
        cases h29260 : x 0 6
        · have f29261 : (x 0 6).toNat = 0 := by rw [h29260]; rfl
          have d29262 : (x 0 2 && x 0 6).toNat = 0 := by
            have r29263 := hand2 (x 0 2) (x 0 6)
            have b29264 := hb (x 0 6)
            have b29265 := hb (x 0 2 && x 0 6)
            clear * - r29263 b29264 b29265 f29261
            omega
          have d29266 : (x 4 2 && x 4 11).toNat = 1 := by
            have r29267 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b29268 := hb (x 0 6)
            have b29269 := hb (x 6 9)
            have b29270 := hb (x 5 1 && x 5 10)
            have b29271 := hb (x 4 2 && x 4 11)
            have b29272 := hb (x 3 3 && x 3 12)
            have b29273 := hb (x 2 4 && x 2 13)
            have b29274 := hb (x 1 5 && x 1 14)
            clear * - r29267 b29268 b29269 b29270 b29271 b29272 b29273 b29274 d28343 d28323 d28240 g34 g35 f29261
            omega
          have d29275 : (x 4 2).toNat = 1 := by
            have r29276 := hand1 (x 4 2) (x 4 11)
            have b29277 := hb (x 4 2)
            have b29278 := hb (x 4 2 && x 4 11)
            clear * - r29276 b29277 b29278 d29266
            omega
          have d29279 : (x 4 14).toNat = 1 := by
            have r29280 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
            have b29281 := hb (x 4 2)
            have b29282 := hb (x 4 14)
            clear * - r29280 b29281 b29282 d29275
            omega
          have d29283 : (x 3 1).toNat = 0 := by
            have r29284 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b29285 := hb (x 3 1)
            have b29286 := hb (x 4 14)
            clear * - r29284 b29285 b29286 d29279
            omega
          have d29287 : (x 3 1 && x 3 11).toNat = 0 := by
            have r29288 := hand1 (x 3 1) (x 3 11)
            have b29289 := hb (x 3 1)
            have b29290 := hb (x 3 1 && x 3 11)
            clear * - r29288 b29289 b29290 d29283
            omega
          have d29291 : (x 4 10).toNat = 1 := by
            have r29292 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b29293 := hb (x (-1) 5)
            have b29294 := hb (x 4 10)
            have b29295 := hb (x 3 1 && x 3 11)
            have b29296 := hb (x 2 2 && x 2 12)
            have b29297 := hb (x 1 3 && x 1 13)
            have b29298 := hb (x 0 4 && x 0 14)
            clear * - r29292 b29293 b29294 b29295 b29296 b29297 b29298 d29287 g38 g39 d27178 g3
            omega
          have d29299 : (x 3 13).toNat = 0 := by
            have r29300 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
            have b29301 := hb (x 3 1)
            have b29302 := hb (x 3 13)
            clear * - r29300 b29301 b29302 d29283
            omega
          have d29303 : (x 3 5).toNat = 0 := by
            have r29304 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
            have b29305 := hb (x 3 5)
            have b29306 := hb (x 3 13)
            clear * - r29304 b29305 b29306 d29299
            omega
          have d29307 : (x 3 5 && x 3 11).toNat = 0 := by
            have r29308 := hand1 (x 3 5) (x 3 11)
            have b29309 := hb (x 3 5)
            have b29310 := hb (x 3 5 && x 3 11)
            clear * - r29308 b29309 b29310 d29303
            omega
          have d29311 : (x 2 1 && x 2 14).toNat = 1 := by
            have r29312 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b29313 := hb (x 1 2)
            have b29314 := hb (x 3 13)
            have b29315 := hb (x 2 1 && x 2 14)
            clear * - r29312 b29313 b29314 b29315 d29299 d27496
            omega
          have d29316 : (x 2 14).toNat = 1 := by
            have r29317 := hand2 (x 2 1) (x 2 14)
            have b29318 := hb (x 2 14)
            have b29319 := hb (x 2 1 && x 2 14)
            clear * - r29317 b29318 b29319 d29311
            omega
          have d29320 : (x 1 1).toNat = 0 := by
            have r29321 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b29322 := hb (x 1 1)
            have b29323 := hb (x 2 14)
            clear * - r29321 b29322 b29323 d29316
            omega
          have d29324 : (x 1 1 && x 1 7).toNat = 0 := by
            have r29325 := hand1 (x 1 1) (x 1 7)
            have b29326 := hb (x 1 1)
            have b29327 := hb (x 1 1 && x 1 7)
            clear * - r29325 b29326 b29327 d29320
            omega
          have d29328 : (x 6 12).toNat = 0 := by
            have r29329 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e29330 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e29331 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b29332 := hb (x 3 3)
            have b29333 := hb (x 4 2)
            have b29334 := hb (x 5 13)
            have b29335 := hb (x 6 12)
            clear * - r29329 e29330 e29331 b29332 b29333 b29334 b29335 d29275
            omega
          have d29336 : (x 5 13).toNat = 0 := by
            have r29337 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e29338 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e29339 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b29340 := hb (x 3 3)
            have b29341 := hb (x 4 2)
            have b29342 := hb (x 5 13)
            have b29343 := hb (x 6 12)
            clear * - r29337 e29338 e29339 b29340 b29341 b29342 b29343 d29328 d29275
            omega
          have d29344 : (x 4 1 && x 4 14).toNat = 1 := by
            have r29345 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b29346 := hb (x 3 2)
            have b29347 := hb (x 5 13)
            have b29348 := hb (x 4 1 && x 4 14)
            clear * - r29345 b29346 b29347 b29348 d29336 d27533
            omega
          have d29349 : (x 4 1).toNat = 1 := by
            have r29350 := hand1 (x 4 1) (x 4 14)
            have b29351 := hb (x 4 1)
            have b29352 := hb (x 4 1 && x 4 14)
            clear * - r29350 b29351 b29352 d29344
            omega
          have d29353 : (x 5 14).toNat = 0 := by
            have r29354 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b29355 := hb (x 4 1)
            have b29356 := hb (x 5 14)
            clear * - r29354 b29355 b29356 d29349
            omega
          have d29357 : (x 5 6).toNat = 0 := by
            have r29358 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
            have b29359 := hb (x 5 6)
            have b29360 := hb (x 5 14)
            clear * - r29358 b29359 b29360 d29353
            omega
          have d29361 : (x 3 3).toNat = 0 := by
            have r29362 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e29363 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e29364 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b29365 := hb (x 3 3)
            have b29366 := hb (x 4 2)
            have b29367 := hb (x 5 13)
            have b29368 := hb (x 6 12)
            clear * - r29362 e29363 e29364 b29365 b29366 b29367 b29368 d29328 d29336 d29275
            omega
          have d29369 : (x 3 11).toNat = 0 := by
            have r29370 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
            have b29371 := hb (x 3 3)
            have b29372 := hb (x 3 11)
            clear * - r29370 b29371 b29372 d29361
            omega
          have d29373 : (x 6 8).toNat = 0 := by
            have r29374 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e29375 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e29376 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e29377 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e29378 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e29379 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e29380 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b29381 := hb (x (-1) 7)
            have b29382 := hb (x 0 6)
            have b29383 := hb (x 1 5)
            have b29384 := hb (x 2 4)
            have b29385 := hb (x 3 11)
            have b29386 := hb (x 4 10)
            have b29387 := hb (x 5 9)
            have b29388 := hb (x 6 8)
            clear * - r29374 e29375 e29376 e29377 e29378 e29379 e29380 b29381 b29382 b29383 b29384 b29385 b29386 b29387 b29388 d29291 d29369 g12 g9 f29261
            omega
          have d29389 : (x 6 2 && x 6 8).toNat = 0 := by
            have r29390 := hand2 (x 6 2) (x 6 8)
            have b29391 := hb (x 6 8)
            have b29392 := hb (x 6 2 && x 6 8)
            clear * - r29390 b29391 b29392 d29373
            omega
          have d29393 : (x 5 9).toNat = 0 := by
            have r29394 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e29395 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e29396 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e29397 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e29398 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e29399 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e29400 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b29401 := hb (x (-1) 7)
            have b29402 := hb (x 0 6)
            have b29403 := hb (x 1 5)
            have b29404 := hb (x 2 4)
            have b29405 := hb (x 3 11)
            have b29406 := hb (x 4 10)
            have b29407 := hb (x 5 9)
            have b29408 := hb (x 6 8)
            clear * - r29394 e29395 e29396 e29397 e29398 e29399 e29400 b29401 b29402 b29403 b29404 b29405 b29406 b29407 b29408 d29373 d29291 d29369 g12 g9 f29261
            omega
          have d29409 : (x 5 3 && x 5 9).toNat = 0 := by
            have r29410 := hand2 (x 5 3) (x 5 9)
            have b29411 := hb (x 5 9)
            have b29412 := hb (x 5 3 && x 5 9)
            clear * - r29410 b29411 b29412 d29393
            omega
          have r29413 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r29414 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r29415 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29416 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
          have e29417 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
          have e29418 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
          have e29419 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
          have e29420 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
          have e29421 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
          have r29422 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29423 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
          have e29424 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
          have e29425 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
          have e29426 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
          have e29427 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
          have e29428 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
          have r29429 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29430 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
          have e29431 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
          have e29432 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
          have e29433 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
          have e29434 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
          have e29435 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
          have r29436 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29437 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
          have e29438 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
          have e29439 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
          have e29440 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
          have e29441 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
          have e29442 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
          have r29443 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29444 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
          have e29445 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
          have r29446 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29447 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
          have e29448 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
          have r29449 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29450 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
          have e29451 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
          have r29452 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29453 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
          have e29454 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
          have r29455 : 1 ≤ (x 12 4).toNat + (x 11 1 && x 11 5).toNat + (x 10 2 && x 10 6).toNat + (x 9 3 && x 9 7).toNat + (x 8 4 && x 8 8).toNat + (x 7 5 && x 7 9).toNat + (x 6 6 && x 6 10).toNat + (x 5 7 && x 5 11).toNat + (x 4 8 && x 4 12).toNat + (x 3 9 && x 3 13).toNat + (x 2 10 && x 2 14).toNat + (x 1 11).toNat := by have q := hcov4 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29456 : (x 11 1 && x 11 5).toNat = (x 11 5).toNat := handr _ _ (fun h => hp13 11 (hp5 11 (h)))
          have e29457 : (x 2 10 && x 2 14).toNat = (x 2 10).toNat := handl _ _ (fun h => hp2 2 (hp10 2 (h)))
          have r29458 : 1 ≤ (x 2 6).toNat + (x 1 1 && x 1 7).toNat + (x 0 2 && x 0 8).toNat + (x (-1) 3 && x (-1) 9).toNat + (x (-2) 4 && x (-2) 10).toNat + (x (-3) 5 && x (-3) 11).toNat + (x (-4) 6 && x (-4) 12).toNat + (x (-5) 7 && x (-5) 13).toNat + (x (-6) 8 && x (-6) 14).toNat + (x (-7) 9).toNat := by have q := hcov6 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r29459 : 1 ≤ (x 8 6).toNat + (x 7 1 && x 7 7).toNat + (x 6 2 && x 6 8).toNat + (x 5 3 && x 5 9).toNat + (x 4 4 && x 4 10).toNat + (x 3 5 && x 3 11).toNat + (x 2 6 && x 2 12).toNat + (x 1 7 && x 1 13).toNat + (x 0 8 && x 0 14).toNat + (x (-1) 9).toNat := by have q := hcov6 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r29460 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r29461 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r29462 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r29463 := hand2 (x (-6) 8) (x (-6) 12)
          have r29464 := hand2 (x (-7) 9) (x (-7) 13)
          have r29465 := hand2 (x 6 2) (x 6 6)
          have r29466 := hand1 (x 5 3) (x 5 7)
          have r29467 := hand2 (x 5 3) (x 5 7)
          have r29468 := hand1 (x 10 2) (x 10 6)
          have r29469 := hand1 (x 9 3) (x 9 7)
          have r29470 := hand2 (x 8 4) (x 8 8)
          have r29471 := hand2 (x 7 5) (x 7 9)
          have r29472 := hand2 (x 6 6) (x 6 10)
          have r29473 := hand1 (x 5 7) (x 5 11)
          have r29474 := hand1 (x (-6) 8) (x (-6) 14)
          have r29475 := hand2 (x 7 1) (x 7 7)
          have r29476 := hand1 (x 4 4) (x 4 10)
          have r29477 := hand2 (x 10 1) (x 10 10)
          have r29478 := hand2 (x 9 2) (x 9 11)
          have r29479 := hand2 (x 8 3) (x 8 12)
          have r29480 := hand1 (x (-8) 2) (x (-8) 12)
          have r29481 := hand1 (x (-9) 3) (x (-9) 13)
          have r29482 := hand1 (x (-10) 4) (x (-10) 14)
          have r29483 := hand1 (x 13 1) (x 13 11)
          have r29484 := hand1 (x 12 2) (x 12 12)
          have r29485 := hand1 (x 11 3) (x 11 13)
          have r29486 := hand1 (x 10 4) (x 10 14)
          linarith only [r29413, r29414, r29415, e29416, e29417, e29418, e29419, e29420, e29421, r29422, e29423, e29424, e29425, e29426, e29427, e29428, r29429, e29430, e29431, e29432, e29433, e29434, e29435, r29436, e29437, e29438, e29439, e29440, e29441, e29442, r29443, e29444, e29445, r29446, e29447, e29448, r29449, e29450, e29451, r29452, e29453, e29454, r29455, e29456, e29457, r29458, r29459, r29460, r29461, r29462, r29463, r29464, r29465, r29466, r29467, r29468, r29469, r29470, r29471, r29472, r29473, r29474, r29475, r29476, r29477, r29478, r29479, r29480, r29481, r29482, r29483, r29484, r29485, r29486, d29184, d29204, d29137, d29040, g4, g5, d29121, g8, g9, d29212, g11, g12, d29092, g13, d29303, d29068, d29369, d29044, d29291, d29357, d29393, d29373, d29262, g14, g15, g16, g17, g18, d29064, d29088, d29208, d29228, d29256, g19, d29060, d29084, d29324, d29252, g20, g21, g22, g23, g24, d29389, d29409, d29307, g25, g26, d29248, d28291, d28307, d29200]
        · have f29611 : (x 0 6).toNat = 1 := by rw [h29260]; rfl
          have d29612 : (x 6 8).toNat = 0 := by
            have r29613 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e29614 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e29615 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e29616 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e29617 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e29618 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e29619 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b29620 := hb (x (-1) 7)
            have b29621 := hb (x 0 6)
            have b29622 := hb (x 1 5)
            have b29623 := hb (x 2 4)
            have b29624 := hb (x 3 11)
            have b29625 := hb (x 4 10)
            have b29626 := hb (x 5 9)
            have b29627 := hb (x 6 8)
            clear * - r29613 e29614 e29615 e29616 e29617 e29618 e29619 b29620 b29621 b29622 b29623 b29624 b29625 b29626 b29627 g12 g9 f29611
            omega
          have d29628 : (x 5 9).toNat = 0 := by
            have r29629 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e29630 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e29631 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e29632 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e29633 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e29634 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e29635 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b29636 := hb (x (-1) 7)
            have b29637 := hb (x 0 6)
            have b29638 := hb (x 1 5)
            have b29639 := hb (x 2 4)
            have b29640 := hb (x 3 11)
            have b29641 := hb (x 4 10)
            have b29642 := hb (x 5 9)
            have b29643 := hb (x 6 8)
            clear * - r29629 e29630 e29631 e29632 e29633 e29634 e29635 b29636 b29637 b29638 b29639 b29640 b29641 b29642 b29643 d29612 g12 g9 f29611
            omega
          have d29644 : (x 4 10).toNat = 0 := by
            have r29645 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e29646 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
            have e29647 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
            have e29648 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
            have e29649 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
            have e29650 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
            have e29651 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
            have b29652 := hb (x (-1) 7)
            have b29653 := hb (x 0 6)
            have b29654 := hb (x 1 5)
            have b29655 := hb (x 2 4)
            have b29656 := hb (x 3 11)
            have b29657 := hb (x 4 10)
            have b29658 := hb (x 5 9)
            have b29659 := hb (x 6 8)
            clear * - r29645 e29646 e29647 e29648 e29649 e29650 e29651 b29652 b29653 b29654 b29655 b29656 b29657 b29658 b29659 d29612 d29628 g12 g9 f29611
            omega
          have d29660 : (x 3 1 && x 3 11).toNat = 1 := by
            have r29661 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b29662 := hb (x (-1) 5)
            have b29663 := hb (x 4 10)
            have b29664 := hb (x 3 1 && x 3 11)
            have b29665 := hb (x 2 2 && x 2 12)
            have b29666 := hb (x 1 3 && x 1 13)
            have b29667 := hb (x 0 4 && x 0 14)
            clear * - r29661 b29662 b29663 b29664 b29665 b29666 b29667 d29644 g38 g39 d27178 g3
            omega
          have d29668 : (x 3 11).toNat = 1 := by
            have r29669 := hand2 (x 3 1) (x 3 11)
            have b29670 := hb (x 3 11)
            have b29671 := hb (x 3 1 && x 3 11)
            clear * - r29669 b29670 b29671 d29660
            omega
          have d29672 : (x 3 3).toNat = 1 := by
            have r29673 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
            have b29674 := hb (x 3 3)
            have b29675 := hb (x 3 11)
            clear * - r29673 b29674 b29675 d29668
            omega
          have d29676 : (x 6 12).toNat = 0 := by
            have r29677 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e29678 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e29679 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b29680 := hb (x 3 3)
            have b29681 := hb (x 4 2)
            have b29682 := hb (x 5 13)
            have b29683 := hb (x 6 12)
            clear * - r29677 e29678 e29679 b29680 b29681 b29682 b29683 d29672
            omega
          have d29684 : (x 5 13).toNat = 0 := by
            have r29685 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e29686 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
            have e29687 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
            have b29688 := hb (x 3 3)
            have b29689 := hb (x 4 2)
            have b29690 := hb (x 5 13)
            have b29691 := hb (x 6 12)
            clear * - r29685 e29686 e29687 b29688 b29689 b29690 b29691 d29676 d29672
            omega
          have d29692 : (x 4 1 && x 4 14).toNat = 1 := by
            have r29693 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b29694 := hb (x 3 2)
            have b29695 := hb (x 5 13)
            have b29696 := hb (x 4 1 && x 4 14)
            clear * - r29693 b29694 b29695 b29696 d29684 d27533
            omega
          have d29697 : (x 4 1).toNat = 1 := by
            have r29698 := hand1 (x 4 1) (x 4 14)
            have b29699 := hb (x 4 1)
            have b29700 := hb (x 4 1 && x 4 14)
            clear * - r29698 b29699 b29700 d29692
            omega
          have d29701 : (x 5 14).toNat = 0 := by
            have r29702 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b29703 := hb (x 4 1)
            have b29704 := hb (x 5 14)
            clear * - r29702 b29703 b29704 d29697
            omega
          have d29705 : (x 5 1 && x 5 14).toNat = 0 := by
            have r29706 := hand2 (x 5 1) (x 5 14)
            have b29707 := hb (x 5 14)
            have b29708 := hb (x 5 1 && x 5 14)
            clear * - r29706 b29707 b29708 d29701
            omega
          have d29709 : (x 4 2).toNat = 1 := by
            have r29710 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b29711 := hb (x 4 2)
            have b29712 := hb (x 6 13)
            have b29713 := hb (x 5 1 && x 5 14)
            clear * - r29710 b29711 b29712 b29713 d28295 d29705
            omega
          have r29714 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e29715 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e29716 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b29717 := hb (x 3 3)
          have b29718 := hb (x 4 2)
          have b29719 := hb (x 5 13)
          have b29720 := hb (x 6 12)
          linarith only [r29714, e29715, e29716, b29717, b29718, b29719, b29720, d29676, d29684, d29709, d29672]

theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_a0 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x (-3) 5).toNat = 0)
    (g2 : (x (-2) 4).toNat = 0)
    (g3 : (x (-1) 5).toNat = 0)
    (g4 : (x (-1) 9).toNat = 0)
    (g5 : (x (-1) 13).toNat = 0)
    (g6 : (x 0 4).toNat = 0)
    (g7 : (x 0 11).toNat = 0)
    (g8 : (x 0 14).toNat = 1)
    (g9 : (x 1 5).toNat = 0)
    (g10 : (x 1 9).toNat = 0)
    (g11 : (x 1 13).toNat = 0)
    (g12 : (x 2 4).toNat = 0)
    (g13 : (x 2 12).toNat = 0)
    (g14 : (x (-1) 3 && x (-1) 7).toNat = 0)
    (g15 : (x (-2) 4 && x (-2) 8).toNat = 0)
    (g16 : (x (-3) 5 && x (-3) 9).toNat = 0)
    (g17 : (x (-4) 6 && x (-4) 10).toNat = 0)
    (g18 : (x (-5) 7 && x (-5) 11).toNat = 0)
    (g19 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g20 : (x (-1) 3 && x (-1) 9).toNat = 0)
    (g21 : (x (-2) 4 && x (-2) 10).toNat = 0)
    (g22 : (x (-3) 5 && x (-3) 11).toNat = 0)
    (g23 : (x (-4) 6 && x (-4) 12).toNat = 0)
    (g24 : (x (-5) 7 && x (-5) 13).toNat = 0)
    (g25 : (x 2 6 && x 2 12).toNat = 0)
    (g26 : (x 1 7 && x 1 13).toNat = 0)
    (g27 : (x 2 8 && x 2 14).toNat = 0)
    (g28 : (x 0 2 && x 0 11).toNat = 0)
    (g29 : (x (-1) 3 && x (-1) 12).toNat = 0)
    (g30 : (x (-2) 4 && x (-2) 13).toNat = 0)
    (g31 : (x (-3) 5 && x (-3) 14).toNat = 0)
    (g32 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g33 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g34 : (x 2 4 && x 2 13).toNat = 0)
    (g35 : (x 1 5 && x 1 14).toNat = 0)
    (g36 : (x (-1) 3 && x (-1) 13).toNat = 0)
    (g37 : (x (-2) 4 && x (-2) 14).toNat = 0)
    (g38 : (x 2 2 && x 2 12).toNat = 0)
    (g39 : (x 1 3 && x 1 13).toNat = 0)
    (g40 : (x 2 4 && x 2 14).toNat = 0)
    (g41 : (x (-1) 1 && x (-1) 12).toNat = 0)
    (g42 : (x (-1) 2 && x (-1) 13).toNat = 0)
    (g43 : (x (-1) 3 && x (-1) 14).toNat = 0)
    (g44 : (x 2 1 && x 2 12).toNat = 0)
    (g45 : (x 1 2 && x 1 13).toNat = 0)
    (g46 : (x (-1) 1 && x (-1) 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_a0_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46
