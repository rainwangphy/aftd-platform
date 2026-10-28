import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1100

Topic: combinatorics   Node: 4bb3047ba272

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_alternates_core: under the layer-free tight-cover constraints for k = 15 and 32 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1100_aux (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x 0 12).toNat = 0)
    (g2 : (x 1 1).toNat = 1)
    (g3 : (x 1 2).toNat = 0)
    (g4 : (x 1 6).toNat = 0)
    (g5 : (x 1 10).toNat = 0)
    (g6 : (x 1 11).toNat = 0)
    (g7 : (x 1 14).toNat = 0)
    (g8 : (x 2 2).toNat = 0)
    (g9 : (x 2 10).toNat = 0)
    (g10 : (x 4 2).toNat = 0)
    (g11 : (x 4 4).toNat = 0)
    (g12 : (x 4 6).toNat = 0)
    (g13 : (x 4 10).toNat = 0)
    (g14 : (x 1 1 && x 1 3).toNat = 0)
    (g15 : (x 0 2 && x 0 4).toNat = 0)
    (g16 : (x 4 7 && x 4 10).toNat = 0)
    (g17 : (x 1 10 && x 1 13).toNat = 0)
    (g18 : (x 4 6 && x 4 10).toNat = 0)
    (g19 : (x 1 1 && x 1 6).toNat = 0)
    (g20 : (x 2 1 && x 2 10).toNat = 0)
    (g21 : (x 1 2 && x 1 11).toNat = 0)
    (g22 : (x 1 1 && x 1 11).toNat = 0)
    (g23 : (x 1 2 && x 1 12).toNat = 0)
    (g24 : (x 2 2 && x 2 12).toNat = 0)
    (g25 : (x 1 3 && x 1 13).toNat = 0)
    (g26 : (x 0 4 && x 0 14).toNat = 0)
    (g27 : (x 2 2 && x 2 13).toNat = 0)
    (g28 : (x 1 3 && x 1 14).toNat = 0)
    (g29 : (x 4 3 && x 4 14).toNat = 0)
    (g30 : (x 1 1 && x 1 14).toNat = 0)
    (g31 : (x 4 1 && x 4 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d28202 : (x 0 1 && x 0 12).toNat = 0 := by
    have r28203 := hand2 (x 0 1) (x 0 12)
    have b28204 := hb (x 0 12)
    have b28205 := hb (x 0 1 && x 0 12)
    clear * - r28203 b28204 b28205 g1
    omega
  have d28206 : (x 0 2 && x 0 12).toNat = 0 := by
    have r28207 := hand2 (x 0 2) (x 0 12)
    have b28208 := hb (x 0 12)
    have b28209 := hb (x 0 2 && x 0 12)
    clear * - r28207 b28208 b28209 g1
    omega
  have d28210 : (x 0 3 && x 0 12).toNat = 0 := by
    have r28211 := hand2 (x 0 3) (x 0 12)
    have b28212 := hb (x 0 12)
    have b28213 := hb (x 0 3 && x 0 12)
    clear * - r28211 b28212 b28213 g1
    omega
  cases h28214 : x 0 2
  · have f28215 : (x 0 2).toNat = 0 := by rw [h28214]; rfl
    have d28216 : (x 2 13).toNat = 1 := by
      have r28217 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28218 := hb (x 0 2)
      have b28219 := hb (x 2 13)
      have b28220 := hb (x 1 1 && x 1 14)
      clear * - r28217 b28218 b28219 b28220 g30 f28215
      omega
    have d28221 : (x 2 1).toNat = 1 := by
      have r28222 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
      have b28223 := hb (x 2 1)
      have b28224 := hb (x 2 13)
      clear * - r28222 b28223 b28224 d28216
      omega
    have d28225 : (x 3 14).toNat = 0 := by
      have r28226 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28227 := hb (x 2 1)
      have b28228 := hb (x 3 14)
      clear * - r28226 b28227 b28228 d28221
      omega
    have d28229 : (x 3 1 && x 3 14).toNat = 0 := by
      have r28230 := hand2 (x 3 1) (x 3 14)
      have b28231 := hb (x 3 14)
      have b28232 := hb (x 3 1 && x 3 14)
      clear * - r28230 b28231 b28232 d28225
      omega
    have d28233 : (x 4 13).toNat = 1 := by
      have r28234 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28235 := hb (x 2 2)
      have b28236 := hb (x 4 13)
      have b28237 := hb (x 3 1 && x 3 14)
      clear * - r28234 b28235 b28236 b28237 d28229 g8
      omega
    have d28238 : (x 4 1).toNat = 1 := by
      have r28239 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
      have b28240 := hb (x 4 1)
      have b28241 := hb (x 4 13)
      clear * - r28239 b28240 b28241 d28233
      omega
    have d28242 : (x 5 14).toNat = 0 := by
      have r28243 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28244 := hb (x 4 1)
      have b28245 := hb (x 5 14)
      clear * - r28243 b28244 b28245 d28238
      omega
    have d28246 : (x 5 1 && x 5 14).toNat = 0 := by
      have r28247 := hand2 (x 5 1) (x 5 14)
      have b28248 := hb (x 5 14)
      have b28249 := hb (x 5 1 && x 5 14)
      clear * - r28247 b28248 b28249 d28242
      omega
    have d28250 : (x 6 13).toNat = 1 := by
      have r28251 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28252 := hb (x 4 2)
      have b28253 := hb (x 6 13)
      have b28254 := hb (x 5 1 && x 5 14)
      clear * - r28251 b28252 b28253 b28254 d28246 g10
      omega
    have d28255 : (x 6 1).toNat = 1 := by
      have r28256 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
      have b28257 := hb (x 6 1)
      have b28258 := hb (x 6 13)
      clear * - r28256 b28257 b28258 d28250
      omega
    have d28259 : (x 7 14).toNat = 0 := by
      have r28260 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28261 := hb (x 6 1)
      have b28262 := hb (x 7 14)
      clear * - r28260 b28261 b28262 d28255
      omega
    have d28263 : (x 7 1 && x 7 14).toNat = 0 := by
      have r28264 := hand2 (x 7 1) (x 7 14)
      have b28265 := hb (x 7 14)
      have b28266 := hb (x 7 1 && x 7 14)
      clear * - r28264 b28265 b28266 d28259
      omega
    have d28267 : (x 7 2).toNat = 0 := by
      have r28268 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
      have b28269 := hb (x 7 2)
      have b28270 := hb (x 7 14)
      clear * - r28268 b28269 b28270 d28259
      omega
    have d28271 : (x 5 2).toNat = 0 := by
      have r28272 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
      have b28273 := hb (x 5 2)
      have b28274 := hb (x 5 14)
      clear * - r28272 b28273 b28274 d28242
      omega
    have d28275 : (x 3 2).toNat = 0 := by
      have r28276 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b28277 := hb (x 3 2)
      have b28278 := hb (x 3 14)
      clear * - r28276 b28277 b28278 d28225
      omega
    have d28279 : (x 5 13).toNat = 1 := by
      have r28280 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28281 := hb (x 3 2)
      have b28282 := hb (x 5 13)
      have b28283 := hb (x 4 1 && x 4 14)
      clear * - r28280 b28281 b28282 b28283 g31 d28275
      omega
    have d28284 : (x 5 1).toNat = 1 := by
      have r28285 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
      have b28286 := hb (x 5 1)
      have b28287 := hb (x 5 13)
      clear * - r28285 b28286 b28287 d28279
      omega
    have d28288 : (x 6 14).toNat = 0 := by
      have r28289 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28290 := hb (x 5 1)
      have b28291 := hb (x 6 14)
      clear * - r28289 b28290 b28291 d28284
      omega
    have d28292 : (x 6 1 && x 6 14).toNat = 0 := by
      have r28293 := hand2 (x 6 1) (x 6 14)
      have b28294 := hb (x 6 14)
      have b28295 := hb (x 6 1 && x 6 14)
      clear * - r28293 b28294 b28295 d28288
      omega
    have d28296 : (x 7 13).toNat = 1 := by
      have r28297 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28298 := hb (x 5 2)
      have b28299 := hb (x 7 13)
      have b28300 := hb (x 6 1 && x 6 14)
      clear * - r28297 b28298 b28299 b28300 d28292 d28271
      omega
    have d28301 : (x 7 1).toNat = 1 := by
      have r28302 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
      have b28303 := hb (x 7 1)
      have b28304 := hb (x 7 13)
      clear * - r28302 b28303 b28304 d28296
      omega
    have d28305 : (x 8 14).toNat = 0 := by
      have r28306 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28307 := hb (x 7 1)
      have b28308 := hb (x 8 14)
      clear * - r28306 b28307 b28308 d28301
      omega
    have d28309 : (x 8 1 && x 8 14).toNat = 0 := by
      have r28310 := hand2 (x 8 1) (x 8 14)
      have b28311 := hb (x 8 14)
      have b28312 := hb (x 8 1 && x 8 14)
      clear * - r28310 b28311 b28312 d28305
      omega
    have d28313 : (x 9 13).toNat = 1 := by
      have r28314 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28315 := hb (x 7 2)
      have b28316 := hb (x 9 13)
      have b28317 := hb (x 8 1 && x 8 14)
      clear * - r28314 b28315 b28316 b28317 d28309 d28267
      omega
    have d28318 : (x 9 1).toNat = 1 := by
      have r28319 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
      have b28320 := hb (x 9 1)
      have b28321 := hb (x 9 13)
      clear * - r28319 b28320 b28321 d28313
      omega
    have d28322 : (x 10 14).toNat = 0 := by
      have r28323 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28324 := hb (x 9 1)
      have b28325 := hb (x 10 14)
      clear * - r28323 b28324 b28325 d28318
      omega
    have d28326 : (x 10 1 && x 10 14).toNat = 0 := by
      have r28327 := hand2 (x 10 1) (x 10 14)
      have b28328 := hb (x 10 14)
      have b28329 := hb (x 10 1 && x 10 14)
      clear * - r28327 b28328 b28329 d28322
      omega
    have d28330 : (x 10 2).toNat = 0 := by
      have r28331 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
      have b28332 := hb (x 10 2)
      have b28333 := hb (x 10 14)
      clear * - r28331 b28332 b28333 d28322
      omega
    have d28334 : (x 8 2).toNat = 0 := by
      have r28335 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
      have b28336 := hb (x 8 2)
      have b28337 := hb (x 8 14)
      clear * - r28335 b28336 b28337 d28305
      omega
    have d28338 : (x 6 2).toNat = 0 := by
      have r28339 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
      have b28340 := hb (x 6 2)
      have b28341 := hb (x 6 14)
      clear * - r28339 b28340 b28341 d28288
      omega
    have d28342 : (x 8 13).toNat = 1 := by
      have r28343 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28344 := hb (x 6 2)
      have b28345 := hb (x 8 13)
      have b28346 := hb (x 7 1 && x 7 14)
      clear * - r28343 b28344 b28345 b28346 d28263 d28338
      omega
    have d28347 : (x 8 1).toNat = 1 := by
      have r28348 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
      have b28349 := hb (x 8 1)
      have b28350 := hb (x 8 13)
      clear * - r28348 b28349 b28350 d28342
      omega
    have d28351 : (x 9 14).toNat = 0 := by
      have r28352 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28353 := hb (x 8 1)
      have b28354 := hb (x 9 14)
      clear * - r28352 b28353 b28354 d28347
      omega
    have d28355 : (x 9 1 && x 9 14).toNat = 0 := by
      have r28356 := hand2 (x 9 1) (x 9 14)
      have b28357 := hb (x 9 14)
      have b28358 := hb (x 9 1 && x 9 14)
      clear * - r28356 b28357 b28358 d28351
      omega
    have d28359 : (x 10 13).toNat = 1 := by
      have r28360 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28361 := hb (x 8 2)
      have b28362 := hb (x 10 13)
      have b28363 := hb (x 9 1 && x 9 14)
      clear * - r28360 b28361 b28362 b28363 d28355 d28334
      omega
    have d28364 : (x 10 1).toNat = 1 := by
      have r28365 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
      have b28366 := hb (x 10 1)
      have b28367 := hb (x 10 13)
      clear * - r28365 b28366 b28367 d28359
      omega
    have d28368 : (x 11 14).toNat = 0 := by
      have r28369 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28370 := hb (x 10 1)
      have b28371 := hb (x 11 14)
      clear * - r28369 b28370 b28371 d28364
      omega
    have d28372 : (x 11 1 && x 11 14).toNat = 0 := by
      have r28373 := hand2 (x 11 1) (x 11 14)
      have b28374 := hb (x 11 14)
      have b28375 := hb (x 11 1 && x 11 14)
      clear * - r28373 b28374 b28375 d28368
      omega
    have d28376 : (x 12 13).toNat = 1 := by
      have r28377 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28378 := hb (x 10 2)
      have b28379 := hb (x 12 13)
      have b28380 := hb (x 11 1 && x 11 14)
      clear * - r28377 b28378 b28379 b28380 d28372 d28330
      omega
    have d28381 : (x 12 1).toNat = 1 := by
      have r28382 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
      have b28383 := hb (x 12 1)
      have b28384 := hb (x 12 13)
      clear * - r28382 b28383 b28384 d28376
      omega
    have d28385 : (x 13 14).toNat = 0 := by
      have r28386 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28387 := hb (x 12 1)
      have b28388 := hb (x 13 14)
      clear * - r28386 b28387 b28388 d28381
      omega
    have d28389 : (x 13 1 && x 13 14).toNat = 0 := by
      have r28390 := hand2 (x 13 1) (x 13 14)
      have b28391 := hb (x 13 14)
      have b28392 := hb (x 13 1 && x 13 14)
      clear * - r28390 b28391 b28392 d28385
      omega
    have d28393 : (x 13 2).toNat = 0 := by
      have r28394 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
      have b28395 := hb (x 13 2)
      have b28396 := hb (x 13 14)
      clear * - r28394 b28395 b28396 d28385
      omega
    have d28397 : (x 11 2).toNat = 0 := by
      have r28398 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
      have b28399 := hb (x 11 2)
      have b28400 := hb (x 11 14)
      clear * - r28398 b28399 b28400 d28368
      omega
    have d28401 : (x 9 2).toNat = 0 := by
      have r28402 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
      have b28403 := hb (x 9 2)
      have b28404 := hb (x 9 14)
      clear * - r28402 b28403 b28404 d28351
      omega
    have d28405 : (x 11 13).toNat = 1 := by
      have r28406 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28407 := hb (x 9 2)
      have b28408 := hb (x 11 13)
      have b28409 := hb (x 10 1 && x 10 14)
      clear * - r28406 b28407 b28408 b28409 d28326 d28401
      omega
    have d28410 : (x 11 1).toNat = 1 := by
      have r28411 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
      have b28412 := hb (x 11 1)
      have b28413 := hb (x 11 13)
      clear * - r28411 b28412 b28413 d28405
      omega
    have d28414 : (x 12 14).toNat = 0 := by
      have r28415 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28416 := hb (x 11 1)
      have b28417 := hb (x 12 14)
      clear * - r28415 b28416 b28417 d28410
      omega
    have d28418 : (x 12 1 && x 12 14).toNat = 0 := by
      have r28419 := hand2 (x 12 1) (x 12 14)
      have b28420 := hb (x 12 14)
      have b28421 := hb (x 12 1 && x 12 14)
      clear * - r28419 b28420 b28421 d28414
      omega
    have d28422 : (x 13 13).toNat = 1 := by
      have r28423 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28424 := hb (x 11 2)
      have b28425 := hb (x 13 13)
      have b28426 := hb (x 12 1 && x 12 14)
      clear * - r28423 b28424 b28425 b28426 d28418 d28397
      omega
    have d28427 : (x 13 1).toNat = 1 := by
      have r28428 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
      have b28429 := hb (x 13 1)
      have b28430 := hb (x 13 13)
      clear * - r28428 b28429 b28430 d28422
      omega
    have d28431 : (x 14 14).toNat = 0 := by
      have r28432 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28433 := hb (x 13 1)
      have b28434 := hb (x 14 14)
      clear * - r28432 b28433 b28434 d28427
      omega
    have d28435 : (x 14 1 && x 14 14).toNat = 0 := by
      have r28436 := hand2 (x 14 1) (x 14 14)
      have b28437 := hb (x 14 14)
      have b28438 := hb (x 14 1 && x 14 14)
      clear * - r28436 b28437 b28438 d28431
      omega
    have d28439 : (x 15 13).toNat = 1 := by
      have r28440 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28441 := hb (x 13 2)
      have b28442 := hb (x 15 13)
      have b28443 := hb (x 14 1 && x 14 14)
      clear * - r28440 b28441 b28442 b28443 d28435 d28393
      omega
    have d28444 : (x 15 1).toNat = 1 := by
      have r28445 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
      have b28446 := hb (x 15 1)
      have b28447 := hb (x 15 13)
      clear * - r28445 b28446 b28447 d28439
      omega
    have d28448 : (x 16 14).toNat = 0 := by
      have r28449 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28450 := hb (x 15 1)
      have b28451 := hb (x 16 14)
      clear * - r28449 b28450 b28451 d28444
      omega
    have d28452 : (x 16 1 && x 16 14).toNat = 0 := by
      have r28453 := hand2 (x 16 1) (x 16 14)
      have b28454 := hb (x 16 14)
      have b28455 := hb (x 16 1 && x 16 14)
      clear * - r28453 b28454 b28455 d28448
      omega
    have d28456 : (x 14 3 && x 14 14).toNat = 0 := by
      have r28457 := hand2 (x 14 3) (x 14 14)
      have b28458 := hb (x 14 14)
      have b28459 := hb (x 14 3 && x 14 14)
      clear * - r28457 b28458 b28459 d28431
      omega
    have d28460 : (x 14 2).toNat = 0 := by
      have r28461 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
      have b28462 := hb (x 14 2)
      have b28463 := hb (x 14 14)
      clear * - r28461 b28462 b28463 d28431
      omega
    have d28464 : (x 12 2).toNat = 0 := by
      have r28465 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
      have b28466 := hb (x 12 2)
      have b28467 := hb (x 12 14)
      clear * - r28465 b28466 b28467 d28414
      omega
    have d28468 : (x 14 13).toNat = 1 := by
      have r28469 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28470 := hb (x 12 2)
      have b28471 := hb (x 14 13)
      have b28472 := hb (x 13 1 && x 13 14)
      clear * - r28469 b28470 b28471 b28472 d28389 d28464
      omega
    have d28473 : (x 14 1).toNat = 1 := by
      have r28474 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
      have b28475 := hb (x 14 1)
      have b28476 := hb (x 14 13)
      clear * - r28474 b28475 b28476 d28468
      omega
    have d28477 : (x 15 14).toNat = 0 := by
      have r28478 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28479 := hb (x 14 1)
      have b28480 := hb (x 15 14)
      clear * - r28478 b28479 b28480 d28473
      omega
    have d28481 : (x 15 1 && x 15 14).toNat = 0 := by
      have r28482 := hand2 (x 15 1) (x 15 14)
      have b28483 := hb (x 15 14)
      have b28484 := hb (x 15 1 && x 15 14)
      clear * - r28482 b28483 b28484 d28477
      omega
    have d28485 : (x 16 13).toNat = 1 := by
      have r28486 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28487 := hb (x 14 2)
      have b28488 := hb (x 16 13)
      have b28489 := hb (x 15 1 && x 15 14)
      clear * - r28486 b28487 b28488 b28489 d28481 d28460
      omega
    have d28490 : (x 16 1).toNat = 1 := by
      have r28491 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
      have b28492 := hb (x 16 1)
      have b28493 := hb (x 16 13)
      clear * - r28491 b28492 b28493 d28485
      omega
    have d28494 : (x 17 14).toNat = 0 := by
      have r28495 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28496 := hb (x 16 1)
      have b28497 := hb (x 17 14)
      clear * - r28495 b28496 b28497 d28490
      omega
    have d28498 : (x 17 2).toNat = 0 := by
      have r28499 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
      have b28500 := hb (x 17 2)
      have b28501 := hb (x 17 14)
      clear * - r28499 b28500 b28501 d28494
      omega
    have d28502 : (x 15 2).toNat = 0 := by
      have r28503 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
      have b28504 := hb (x 15 2)
      have b28505 := hb (x 15 14)
      clear * - r28503 b28504 b28505 d28477
      omega
    have d28506 : (x 15 2 && x 15 13).toNat = 0 := by
      have r28507 := hand1 (x 15 2) (x 15 13)
      have b28508 := hb (x 15 2)
      have b28509 := hb (x 15 2 && x 15 13)
      clear * - r28507 b28508 b28509 d28502
      omega
    have d28510 : (x 17 13).toNat = 1 := by
      have r28511 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28512 := hb (x 15 2)
      have b28513 := hb (x 17 13)
      have b28514 := hb (x 16 1 && x 16 14)
      clear * - r28511 b28512 b28513 b28514 d28452 d28502
      omega
    have d28515 : (x 17 1).toNat = 1 := by
      have r28516 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
      have b28517 := hb (x 17 1)
      have b28518 := hb (x 17 13)
      clear * - r28516 b28517 b28518 d28510
      omega
    have d28519 : (x 18 14).toNat = 0 := by
      have r28520 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28521 := hb (x 17 1)
      have b28522 := hb (x 18 14)
      clear * - r28520 b28521 b28522 d28515
      omega
    have d28523 : (x 18 1 && x 18 14).toNat = 0 := by
      have r28524 := hand2 (x 18 1) (x 18 14)
      have b28525 := hb (x 18 14)
      have b28526 := hb (x 18 1 && x 18 14)
      clear * - r28524 b28525 b28526 d28519
      omega
    have d28527 : (x 19 13).toNat = 1 := by
      have r28528 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28529 := hb (x 17 2)
      have b28530 := hb (x 19 13)
      have b28531 := hb (x 18 1 && x 18 14)
      clear * - r28528 b28529 b28530 b28531 d28523 d28498
      omega
    have d28532 : (x 18 2).toNat = 0 := by
      have r28533 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
      have b28534 := hb (x 18 2)
      have b28535 := hb (x 18 14)
      clear * - r28533 b28534 b28535 d28519
      omega
    have d28536 : (x 20 12).toNat = 0 := by
      have r28537 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28538 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e28539 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b28540 := hb (x 17 3)
      have b28541 := hb (x 18 2)
      have b28542 := hb (x 19 13)
      have b28543 := hb (x 20 12)
      clear * - r28537 e28538 e28539 b28540 b28541 b28542 b28543 d28527 d28532
      omega
    have d28544 : (x 17 3).toNat = 0 := by
      have r28545 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28546 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e28547 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b28548 := hb (x 17 3)
      have b28549 := hb (x 18 2)
      have b28550 := hb (x 19 13)
      have b28551 := hb (x 20 12)
      clear * - r28545 e28546 e28547 b28548 b28549 b28550 b28551 d28536 d28527 d28532
      omega
    have d28552 : (x 17 11).toNat = 0 := by
      have r28553 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
      have b28554 := hb (x 17 3)
      have b28555 := hb (x 17 11)
      clear * - r28553 b28554 b28555 d28544
      omega
    have d28556 : (x 16 12).toNat = 0 := by
      have r28557 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28558 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e28559 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b28560 := hb (x 13 3)
      have b28561 := hb (x 14 2)
      have b28562 := hb (x 15 13)
      have b28563 := hb (x 16 12)
      clear * - r28557 e28558 e28559 b28560 b28561 b28562 b28563 d28439 d28460
      omega
    have d28564 : (x 16 1 && x 16 12).toNat = 0 := by
      have r28565 := hand2 (x 16 1) (x 16 12)
      have b28566 := hb (x 16 12)
      have b28567 := hb (x 16 1 && x 16 12)
      clear * - r28565 b28566 b28567 d28556
      omega
    have d28568 : (x 13 12).toNat = 0 := by
      have r28569 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28570 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e28571 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b28572 := hb (x 10 3)
      have b28573 := hb (x 11 2)
      have b28574 := hb (x 12 13)
      have b28575 := hb (x 13 12)
      clear * - r28569 e28570 e28571 b28572 b28573 b28574 b28575 d28376 d28397
      omega
    have d28576 : (x 13 4).toNat = 0 := by
      have r28577 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
      have b28578 := hb (x 13 4)
      have b28579 := hb (x 13 12)
      clear * - r28577 b28578 b28579 d28568
      omega
    have r28580 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b28581 := hb (x 13 4)
    have b28582 := hb (x 17 11)
    have b28583 := hb (x 16 1 && x 16 12)
    have b28584 := hb (x 15 2 && x 15 13)
    have b28585 := hb (x 14 3 && x 14 14)
    linarith only [r28580, b28581, b28582, b28583, b28584, b28585, d28552, d28564, d28506, d28456, d28576]
  · have f28586 : (x 0 2).toNat = 1 := by rw [h28214]; rfl
    have d28587 : (x 0 14).toNat = 1 := by
      have r28588 : (x 0 2).toNat ≤ (x 0 14).toNat := himp _ _ (hp2 0)
      have b28589 := hb (x 0 2)
      have b28590 := hb (x 0 14)
      clear * - r28588 b28589 b28590 f28586
      omega
    have d28591 : (x (-1) 1).toNat = 0 := by
      have r28592 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28593 := hb (x (-1) 1)
      have b28594 := hb (x 0 14)
      clear * - r28592 b28593 b28594 d28587
      omega
    have d28595 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
      have r28596 := hand1 (x (-1) 1) (x (-1) 14)
      have b28597 := hb (x (-1) 1)
      have b28598 := hb (x (-1) 1 && x (-1) 14)
      clear * - r28596 b28597 b28598 d28591
      omega
    have d28599 : (x (-1) 13).toNat = 0 := by
      have r28600 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
      have b28601 := hb (x (-1) 1)
      have b28602 := hb (x (-1) 13)
      clear * - r28600 b28601 b28602 d28591
      omega
    have d28603 : (x (-1) 2 && x (-1) 13).toNat = 0 := by
      have r28604 := hand2 (x (-1) 2) (x (-1) 13)
      have b28605 := hb (x (-1) 13)
      have b28606 := hb (x (-1) 2 && x (-1) 13)
      clear * - r28604 b28605 b28606 d28599
      omega
    have d28607 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
      have r28608 := hand2 (x (-1) 3) (x (-1) 13)
      have b28609 := hb (x (-1) 13)
      have b28610 := hb (x (-1) 3 && x (-1) 13)
      clear * - r28608 b28609 b28610 d28599
      omega
    have d28611 : (x (-1) 4 && x (-1) 13).toNat = 0 := by
      have r28612 := hand2 (x (-1) 4) (x (-1) 13)
      have b28613 := hb (x (-1) 13)
      have b28614 := hb (x (-1) 4 && x (-1) 13)
      clear * - r28612 b28613 b28614 d28599
      omega
    have d28615 : (x (-1) 5).toNat = 0 := by
      have r28616 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
      have b28617 := hb (x (-1) 5)
      have b28618 := hb (x (-1) 13)
      clear * - r28616 b28617 b28618 d28599
      omega
    have d28619 : (x (-1) 3 && x (-1) 5).toNat = 0 := by
      have r28620 := hand2 (x (-1) 3) (x (-1) 5)
      have b28621 := hb (x (-1) 5)
      have b28622 := hb (x (-1) 3 && x (-1) 5)
      clear * - r28620 b28621 b28622 d28615
      omega
    have d28623 : (x (-1) 9).toNat = 0 := by
      have r28624 : (x (-1) 9).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp9 (-1))
      have b28625 := hb (x (-1) 1)
      have b28626 := hb (x (-1) 9)
      clear * - r28624 b28625 b28626 d28591
      omega
    have d28627 : (x 2 12).toNat = 0 := by
      have r28628 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28629 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e28630 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b28631 := hb (x (-1) 3)
      have b28632 := hb (x 0 2)
      have b28633 := hb (x 1 13)
      have b28634 := hb (x 2 12)
      clear * - r28628 e28629 e28630 b28631 b28632 b28633 b28634 f28586
      omega
    have d28635 : (x 2 8 && x 2 12).toNat = 0 := by
      have r28636 := hand2 (x 2 8) (x 2 12)
      have b28637 := hb (x 2 12)
      have b28638 := hb (x 2 8 && x 2 12)
      clear * - r28636 b28637 b28638 d28627
      omega
    have d28639 : (x 2 9 && x 2 12).toNat = 0 := by
      have r28640 := hand2 (x 2 9) (x 2 12)
      have b28641 := hb (x 2 12)
      have b28642 := hb (x 2 9 && x 2 12)
      clear * - r28640 b28641 b28642 d28627
      omega
    have d28643 : (x 2 4).toNat = 0 := by
      have r28644 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
      have b28645 := hb (x 2 4)
      have b28646 := hb (x 2 12)
      clear * - r28644 b28645 b28646 d28627
      omega
    have d28647 : (x 1 13).toNat = 0 := by
      have r28648 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28649 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e28650 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b28651 := hb (x (-1) 3)
      have b28652 := hb (x 0 2)
      have b28653 := hb (x 1 13)
      have b28654 := hb (x 2 12)
      clear * - r28648 e28649 e28650 b28651 b28652 b28653 b28654 d28627 f28586
      omega
    have d28655 : (x 1 9 && x 1 13).toNat = 0 := by
      have r28656 := hand2 (x 1 9) (x 1 13)
      have b28657 := hb (x 1 13)
      have b28658 := hb (x 1 9 && x 1 13)
      clear * - r28656 b28657 b28658 d28647
      omega
    have d28659 : (x 1 5).toNat = 0 := by
      have r28660 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
      have b28661 := hb (x 1 5)
      have b28662 := hb (x 1 13)
      clear * - r28660 b28661 b28662 d28647
      omega
    have d28663 : (x (-1) 3).toNat = 0 := by
      have r28664 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28665 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e28666 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b28667 := hb (x (-1) 3)
      have b28668 := hb (x 0 2)
      have b28669 := hb (x 1 13)
      have b28670 := hb (x 2 12)
      clear * - r28664 e28665 e28666 b28667 b28668 b28669 b28670 d28627 d28647 f28586
      omega
    have d28671 : (x (-1) 3 && x (-1) 8).toNat = 0 := by
      have r28672 := hand1 (x (-1) 3) (x (-1) 8)
      have b28673 := hb (x (-1) 3)
      have b28674 := hb (x (-1) 3 && x (-1) 8)
      clear * - r28672 b28673 b28674 d28663
      omega
    have d28675 : (x (-1) 3 && x (-1) 7).toNat = 0 := by
      have r28676 := hand1 (x (-1) 3) (x (-1) 7)
      have b28677 := hb (x (-1) 3)
      have b28678 := hb (x (-1) 3 && x (-1) 7)
      clear * - r28676 b28677 b28678 d28663
      omega
    have d28679 : (x (-1) 11).toNat = 0 := by
      have r28680 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b28681 := hb (x (-1) 3)
      have b28682 := hb (x (-1) 11)
      clear * - r28680 b28681 b28682 d28663
      omega
    have d28683 : (x 3 1 && x 3 11).toNat = 1 := by
      have r28684 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28685 := hb (x (-1) 5)
      have b28686 := hb (x 4 10)
      have b28687 := hb (x 3 1 && x 3 11)
      have b28688 := hb (x 2 2 && x 2 12)
      have b28689 := hb (x 1 3 && x 1 13)
      have b28690 := hb (x 0 4 && x 0 14)
      clear * - r28684 b28685 b28686 b28687 b28688 b28689 b28690 g13 g24 g25 g26 d28615
      omega
    have d28691 : (x 3 11).toNat = 1 := by
      have r28692 := hand2 (x 3 1) (x 3 11)
      have b28693 := hb (x 3 11)
      have b28694 := hb (x 3 1 && x 3 11)
      clear * - r28692 b28693 b28694 d28683
      omega
    have d28695 : (x 3 3).toNat = 1 := by
      have r28696 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b28697 := hb (x 3 3)
      have b28698 := hb (x 3 11)
      clear * - r28696 b28697 b28698 d28691
      omega
    have d28699 : (x 6 12).toNat = 0 := by
      have r28700 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28701 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e28702 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b28703 := hb (x 3 3)
      have b28704 := hb (x 4 2)
      have b28705 := hb (x 5 13)
      have b28706 := hb (x 6 12)
      clear * - r28700 e28701 e28702 b28703 b28704 b28705 b28706 g10 d28695
      omega
    have d28707 : (x 6 1 && x 6 12).toNat = 0 := by
      have r28708 := hand2 (x 6 1) (x 6 12)
      have b28709 := hb (x 6 12)
      have b28710 := hb (x 6 1 && x 6 12)
      clear * - r28708 b28709 b28710 d28699
      omega
    have d28711 : (x 6 4).toNat = 0 := by
      have r28712 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
      have b28713 := hb (x 6 4)
      have b28714 := hb (x 6 12)
      clear * - r28712 b28713 b28714 d28699
      omega
    have d28715 : (x 6 4 && x 6 14).toNat = 0 := by
      have r28716 := hand1 (x 6 4) (x 6 14)
      have b28717 := hb (x 6 4)
      have b28718 := hb (x 6 4 && x 6 14)
      clear * - r28716 b28717 b28718 d28711
      omega
    have d28719 : (x 6 4 && x 6 8).toNat = 0 := by
      have r28720 := hand1 (x 6 4) (x 6 8)
      have b28721 := hb (x 6 4)
      have b28722 := hb (x 6 4 && x 6 8)
      clear * - r28720 b28721 b28722 d28711
      omega
    have d28723 : (x 5 13).toNat = 0 := by
      have r28724 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28725 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e28726 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b28727 := hb (x 3 3)
      have b28728 := hb (x 4 2)
      have b28729 := hb (x 5 13)
      have b28730 := hb (x 6 12)
      clear * - r28724 e28725 e28726 b28727 b28728 b28729 b28730 d28699 g10 d28695
      omega
    have d28731 : (x 5 2 && x 5 13).toNat = 0 := by
      have r28732 := hand2 (x 5 2) (x 5 13)
      have b28733 := hb (x 5 13)
      have b28734 := hb (x 5 2 && x 5 13)
      clear * - r28732 b28733 b28734 d28723
      omega
    have d28735 : (x 5 5).toNat = 0 := by
      have r28736 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
      have b28737 := hb (x 5 5)
      have b28738 := hb (x 5 13)
      clear * - r28736 b28737 b28738 d28723
      omega
    have d28739 : (x 5 5 && x 5 9).toNat = 0 := by
      have r28740 := hand1 (x 5 5) (x 5 9)
      have b28741 := hb (x 5 5)
      have b28742 := hb (x 5 5 && x 5 9)
      clear * - r28740 b28741 b28742 d28735
      omega
    have d28743 : (x 3 2).toNat = 1 := by
      have r28744 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28745 := hb (x 3 2)
      have b28746 := hb (x 5 13)
      have b28747 := hb (x 4 1 && x 4 14)
      clear * - r28744 b28745 b28746 b28747 d28723 g31
      omega
    have d28748 : (x 3 14).toNat = 1 := by
      have r28749 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b28750 := hb (x 3 2)
      have b28751 := hb (x 3 14)
      clear * - r28749 b28750 b28751 d28743
      omega
    have d28752 : (x 2 1).toNat = 0 := by
      have r28753 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b28754 := hb (x 2 1)
      have b28755 := hb (x 3 14)
      clear * - r28753 b28754 b28755 d28748
      omega
    have d28756 : (x 2 1 && x 2 11).toNat = 0 := by
      have r28757 := hand1 (x 2 1) (x 2 11)
      have b28758 := hb (x 2 1)
      have b28759 := hb (x 2 1 && x 2 11)
      clear * - r28757 b28758 b28759 d28752
      omega
    have d28760 : (x 2 13).toNat = 0 := by
      have r28761 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
      have b28762 := hb (x 2 1)
      have b28763 := hb (x 2 13)
      clear * - r28761 b28762 b28763 d28752
      omega
    have d28764 : (x 2 5).toNat = 0 := by
      have r28765 : (x 2 5).toNat ≤ (x 2 13).toNat := himp _ _ (hp5 2)
      have b28766 := hb (x 2 5)
      have b28767 := hb (x 2 13)
      clear * - r28765 b28766 b28767 d28760
      omega
    have d28768 : (x 2 9).toNat = 0 := by
      have r28769 : (x 2 9).toNat ≤ (x 2 1).toNat := himp _ _ (hp9 2)
      have b28770 := hb (x 2 1)
      have b28771 := hb (x 2 9)
      clear * - r28769 b28770 b28771 d28752
      omega
    have d28772 : (x 5 12).toNat = 0 := by
      have r28773 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28774 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e28775 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b28776 := hb (x 2 3)
      have b28777 := hb (x 3 2)
      have b28778 := hb (x 4 13)
      have b28779 := hb (x 5 12)
      clear * - r28773 e28774 e28775 b28776 b28777 b28778 b28779 d28743
      omega
    have d28780 : (x 4 13).toNat = 0 := by
      have r28781 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28782 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e28783 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b28784 := hb (x 2 3)
      have b28785 := hb (x 3 2)
      have b28786 := hb (x 4 13)
      have b28787 := hb (x 5 12)
      clear * - r28781 e28782 e28783 b28784 b28785 b28786 b28787 d28772 d28743
      omega
    have d28788 : (x 2 3).toNat = 0 := by
      have r28789 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28790 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e28791 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b28792 := hb (x 2 3)
      have b28793 := hb (x 3 2)
      have b28794 := hb (x 4 13)
      have b28795 := hb (x 5 12)
      clear * - r28789 e28790 e28791 b28792 b28793 b28794 b28795 d28772 d28780 d28743
      omega
    have d28796 : (x 2 11).toNat = 0 := by
      have r28797 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
      have b28798 := hb (x 2 3)
      have b28799 := hb (x 2 11)
      clear * - r28797 b28798 b28799 d28788
      omega
    have d28800 : (x 6 8).toNat = 0 := by
      have r28801 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28802 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e28803 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e28804 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e28805 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e28806 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e28807 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b28808 := hb (x (-1) 7)
      have b28809 := hb (x 0 6)
      have b28810 := hb (x 1 5)
      have b28811 := hb (x 2 4)
      have b28812 := hb (x 3 11)
      have b28813 := hb (x 4 10)
      have b28814 := hb (x 5 9)
      have b28815 := hb (x 6 8)
      clear * - r28801 e28802 e28803 e28804 e28805 e28806 e28807 b28808 b28809 b28810 b28811 b28812 b28813 b28814 b28815 g13 d28691 d28643 d28659
      omega
    have d28816 : (x 6 5 && x 6 8).toNat = 0 := by
      have r28817 := hand2 (x 6 5) (x 6 8)
      have b28818 := hb (x 6 8)
      have b28819 := hb (x 6 5 && x 6 8)
      clear * - r28817 b28818 b28819 d28800
      omega
    have d28820 : (x 5 9).toNat = 0 := by
      have r28821 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28822 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e28823 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e28824 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e28825 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e28826 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e28827 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b28828 := hb (x (-1) 7)
      have b28829 := hb (x 0 6)
      have b28830 := hb (x 1 5)
      have b28831 := hb (x 2 4)
      have b28832 := hb (x 3 11)
      have b28833 := hb (x 4 10)
      have b28834 := hb (x 5 9)
      have b28835 := hb (x 6 8)
      clear * - r28821 e28822 e28823 e28824 e28825 e28826 e28827 b28828 b28829 b28830 b28831 b28832 b28833 b28834 b28835 d28800 g13 d28691 d28643 d28659
      omega
    have d28836 : (x 5 6 && x 5 9).toNat = 0 := by
      have r28837 := hand2 (x 5 6) (x 5 9)
      have b28838 := hb (x 5 9)
      have b28839 := hb (x 5 6 && x 5 9)
      clear * - r28837 b28838 b28839 d28820
      omega
    have d28840 : (x 0 6).toNat = 0 := by
      have r28841 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e28842 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e28843 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e28844 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e28845 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e28846 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e28847 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b28848 := hb (x (-1) 7)
      have b28849 := hb (x 0 6)
      have b28850 := hb (x 1 5)
      have b28851 := hb (x 2 4)
      have b28852 := hb (x 3 11)
      have b28853 := hb (x 4 10)
      have b28854 := hb (x 5 9)
      have b28855 := hb (x 6 8)
      clear * - r28841 e28842 e28843 e28844 e28845 e28846 e28847 b28848 b28849 b28850 b28851 b28852 b28853 b28854 b28855 d28800 d28820 g13 d28691 d28643 d28659
      omega
    have d28856 : (x 0 2 && x 0 6).toNat = 0 := by
      have r28857 := hand2 (x 0 2) (x 0 6)
      have b28858 := hb (x 0 6)
      have b28859 := hb (x 0 2 && x 0 6)
      clear * - r28857 b28858 b28859 d28840
      omega
    cases h28860 : x 0 3
    · have f28861 : (x 0 3).toNat = 0 := by rw [h28860]; rfl
      have d28862 : (x 0 3 && x 0 13).toNat = 0 := by
        have r28863 := hand1 (x 0 3) (x 0 13)
        have b28864 := hb (x 0 3)
        have b28865 := hb (x 0 3 && x 0 13)
        clear * - r28863 b28864 b28865 f28861
        omega
      have d28866 : (x 0 11).toNat = 0 := by
        have r28867 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
        have b28868 := hb (x 0 3)
        have b28869 := hb (x 0 11)
        clear * - r28867 b28868 b28869 f28861
        omega
      have d28870 : (x 0 1 && x 0 11).toNat = 0 := by
        have r28871 := hand2 (x 0 1) (x 0 11)
        have b28872 := hb (x 0 11)
        have b28873 := hb (x 0 1 && x 0 11)
        clear * - r28871 b28872 b28873 d28866
        omega
      have d28874 : (x 0 11 && x 0 14).toNat = 0 := by
        have r28875 := hand1 (x 0 11) (x 0 14)
        have b28876 := hb (x 0 11)
        have b28877 := hb (x 0 11 && x 0 14)
        clear * - r28875 b28876 b28877 d28866
        omega
      have d28878 : (x 3 12).toNat = 1 := by
        have r28879 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e28880 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e28881 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b28882 := hb (x 0 3)
        have b28883 := hb (x 1 2)
        have b28884 := hb (x 2 13)
        have b28885 := hb (x 3 12)
        clear * - r28879 e28880 e28881 b28882 b28883 b28884 b28885 d28760 g3 f28861
        omega
      cases h28886 : x 0 5
      · have f28887 : (x 0 5).toNat = 0 := by rw [h28886]; rfl
        cases h28888 : x 0 7
        · have f28889 : (x 0 7).toNat = 0 := by rw [h28888]; rfl
          have d28890 : (x 0 2 && x 0 7).toNat = 0 := by
            have r28891 := hand2 (x 0 2) (x 0 7)
            have b28892 := hb (x 0 7)
            have b28893 := hb (x 0 2 && x 0 7)
            clear * - r28891 b28892 b28893 f28889
            omega
          cases h28894 : x 0 8
          · have f28895 : (x 0 8).toNat = 0 := by rw [h28894]; rfl
            cases h28896 : x 0 10
            · have f28897 : (x 0 10).toNat = 0 := by rw [h28896]; rfl
              cases h28898 : x 0 13
              · have f28899 : (x 0 13).toNat = 0 := by rw [h28898]; rfl
                have d28900 : (x (-2) 2).toNat = 1 := by
                  have r28901 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b28902 := hb (x (-2) 2)
                  have b28903 := hb (x 0 13)
                  have b28904 := hb (x (-1) 1 && x (-1) 14)
                  clear * - r28901 b28902 b28903 b28904 f28899 d28595
                  omega
                have d28905 : (x (-2) 14).toNat = 1 := by
                  have r28906 : (x (-2) 2).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp2 (-2))
                  have b28907 := hb (x (-2) 2)
                  have b28908 := hb (x (-2) 14)
                  clear * - r28906 b28907 b28908 d28900
                  omega
                have d28909 : (x (-3) 1).toNat = 0 := by
                  have r28910 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b28911 := hb (x (-3) 1)
                  have b28912 := hb (x (-2) 14)
                  clear * - r28910 b28911 b28912 d28905
                  omega
                have d28913 : (x (-3) 1 && x (-3) 14).toNat = 0 := by
                  have r28914 := hand1 (x (-3) 1) (x (-3) 14)
                  have b28915 := hb (x (-3) 1)
                  have b28916 := hb (x (-3) 1 && x (-3) 14)
                  clear * - r28914 b28915 b28916 d28909
                  omega
                have d28917 : (x (-3) 13).toNat = 0 := by
                  have r28918 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                  have b28919 := hb (x (-3) 1)
                  have b28920 := hb (x (-3) 13)
                  clear * - r28918 b28919 b28920 d28909
                  omega
                have d28921 : (x (-3) 5).toNat = 0 := by
                  have r28922 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
                  have b28923 := hb (x (-3) 5)
                  have b28924 := hb (x (-3) 13)
                  clear * - r28922 b28923 b28924 d28917
                  omega
                have d28925 : (x (-3) 5 && x (-3) 10).toNat = 0 := by
                  have r28926 := hand1 (x (-3) 5) (x (-3) 10)
                  have b28927 := hb (x (-3) 5)
                  have b28928 := hb (x (-3) 5 && x (-3) 10)
                  clear * - r28926 b28927 b28928 d28921
                  omega
                have d28929 : (x (-3) 3).toNat = 0 := by
                  have r28930 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e28931 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
                  have e28932 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
                  have b28933 := hb (x (-3) 3)
                  have b28934 := hb (x (-2) 2)
                  have b28935 := hb (x (-1) 13)
                  have b28936 := hb (x 0 12)
                  clear * - r28930 e28931 e28932 b28933 b28934 b28935 b28936 g1 d28599 d28900
                  omega
                have d28937 : (x (-3) 11).toNat = 0 := by
                  have r28938 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
                  have b28939 := hb (x (-3) 3)
                  have b28940 := hb (x (-3) 11)
                  clear * - r28938 b28939 b28940 d28929
                  omega
                have d28941 : (x (-3) 2 && x (-3) 11).toNat = 0 := by
                  have r28942 := hand2 (x (-3) 2) (x (-3) 11)
                  have b28943 := hb (x (-3) 11)
                  have b28944 := hb (x (-3) 2 && x (-3) 11)
                  clear * - r28942 b28943 b28944 d28937
                  omega
                have d28945 : (x (-2) 4 && x (-2) 14).toNat = 1 := by
                  have r28946 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b28947 := hb (x (-3) 5)
                  have b28948 := hb (x 2 10)
                  have b28949 := hb (x 1 1 && x 1 11)
                  have b28950 := hb (x 0 2 && x 0 12)
                  have b28951 := hb (x (-1) 3 && x (-1) 13)
                  have b28952 := hb (x (-2) 4 && x (-2) 14)
                  clear * - r28946 b28947 b28948 b28949 b28950 b28951 b28952 g9 g22 d28206 d28607 d28921
                  omega
                have d28953 : (x (-2) 4).toNat = 1 := by
                  have r28954 := hand1 (x (-2) 4) (x (-2) 14)
                  have b28955 := hb (x (-2) 4)
                  have b28956 := hb (x (-2) 4 && x (-2) 14)
                  clear * - r28954 b28955 b28956 d28945
                  omega
                have d28957 : (x (-2) 12).toNat = 1 := by
                  have r28958 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
                  have b28959 := hb (x (-2) 4)
                  have b28960 := hb (x (-2) 12)
                  clear * - r28958 b28959 b28960 d28953
                  omega
                have d28961 : (x (-4) 2).toNat = 0 := by
                  have r28962 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e28963 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                  have e28964 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                  have b28965 := hb (x (-5) 3)
                  have b28966 := hb (x (-4) 2)
                  have b28967 := hb (x (-3) 13)
                  have b28968 := hb (x (-2) 12)
                  clear * - r28962 e28963 e28964 b28965 b28966 b28967 b28968 d28957 d28917
                  omega
                have d28969 : (x (-2) 13).toNat = 1 := by
                  have r28970 : 1 ≤ (x (-2) 13).toNat + (x (-3) 1 && x (-3) 14).toNat + (x (-4) 2).toNat := by have q := hcov13 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b28971 := hb (x (-4) 2)
                  have b28972 := hb (x (-2) 13)
                  have b28973 := hb (x (-3) 1 && x (-3) 14)
                  clear * - r28970 b28971 b28972 b28973 d28913 d28961
                  omega
                have d28974 : (x (-2) 1).toNat = 1 := by
                  have r28975 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
                  have b28976 := hb (x (-2) 1)
                  have b28977 := hb (x (-2) 13)
                  clear * - r28975 b28976 b28977 d28969
                  omega
                have d28978 : (x (-1) 12).toNat = 0 := by
                  have r28979 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e28980 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e28981 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b28982 := hb (x (-4) 3)
                  have b28983 := hb (x (-3) 2)
                  have b28984 := hb (x (-2) 13)
                  have b28985 := hb (x (-1) 12)
                  clear * - r28979 e28980 e28981 b28982 b28983 b28984 b28985 d28969
                  omega
                have d28986 : (x (-3) 2).toNat = 0 := by
                  have r28987 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e28988 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e28989 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b28990 := hb (x (-4) 3)
                  have b28991 := hb (x (-3) 2)
                  have b28992 := hb (x (-2) 13)
                  have b28993 := hb (x (-1) 12)
                  clear * - r28987 e28988 e28989 b28990 b28991 b28992 b28993 d28978 d28969
                  omega
                have d28994 : (x (-3) 10).toNat = 0 := by
                  have r28995 : (x (-3) 10).toNat ≤ (x (-3) 2).toNat := himp _ _ (hp10 (-3))
                  have b28996 := hb (x (-3) 2)
                  have b28997 := hb (x (-3) 10)
                  clear * - r28995 b28996 b28997 d28986
                  omega
                have d28998 : (x (-4) 3).toNat = 0 := by
                  have r28999 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29000 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e29001 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b29002 := hb (x (-4) 3)
                  have b29003 := hb (x (-3) 2)
                  have b29004 := hb (x (-2) 13)
                  have b29005 := hb (x (-1) 12)
                  clear * - r28999 e29000 e29001 b29002 b29003 b29004 b29005 d28978 d28969 d28986
                  omega
                have d29006 : (x (-4) 3 && x (-4) 12).toNat = 0 := by
                  have r29007 := hand1 (x (-4) 3) (x (-4) 12)
                  have b29008 := hb (x (-4) 3)
                  have b29009 := hb (x (-4) 3 && x (-4) 12)
                  clear * - r29007 b29008 b29009 d28998
                  omega
                have d29010 : (x (-4) 11).toNat = 0 := by
                  have r29011 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
                  have b29012 := hb (x (-4) 3)
                  have b29013 := hb (x (-4) 11)
                  clear * - r29011 b29012 b29013 d28998
                  omega
                have d29014 : (x (-4) 6 && x (-4) 11).toNat = 0 := by
                  have r29015 := hand2 (x (-4) 6) (x (-4) 11)
                  have b29016 := hb (x (-4) 11)
                  have b29017 := hb (x (-4) 6 && x (-4) 11)
                  clear * - r29015 b29016 b29017 d29010
                  omega
                have d29018 : (x 2 8).toNat = 0 := by
                  have r29019 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29020 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e29021 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e29022 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e29023 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e29024 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e29025 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b29026 := hb (x (-5) 7)
                  have b29027 := hb (x (-4) 6)
                  have b29028 := hb (x (-3) 5)
                  have b29029 := hb (x (-2) 4)
                  have b29030 := hb (x (-1) 11)
                  have b29031 := hb (x 0 10)
                  have b29032 := hb (x 1 9)
                  have b29033 := hb (x 2 8)
                  clear * - r29019 e29020 e29021 e29022 e29023 e29024 e29025 b29026 b29027 b29028 b29029 b29030 b29031 b29032 b29033 f28897 d28679 d28953 d28921
                  omega
                have d29034 : (x 1 9).toNat = 0 := by
                  have r29035 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29036 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e29037 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e29038 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e29039 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e29040 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e29041 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b29042 := hb (x (-5) 7)
                  have b29043 := hb (x (-4) 6)
                  have b29044 := hb (x (-3) 5)
                  have b29045 := hb (x (-2) 4)
                  have b29046 := hb (x (-1) 11)
                  have b29047 := hb (x 0 10)
                  have b29048 := hb (x 1 9)
                  have b29049 := hb (x 2 8)
                  clear * - r29035 e29036 e29037 e29038 e29039 e29040 e29041 b29042 b29043 b29044 b29045 b29046 b29047 b29048 b29049 d29018 f28897 d28679 d28953 d28921
                  omega
                have d29050 : (x (-4) 6).toNat = 0 := by
                  have r29051 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29052 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e29053 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e29054 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e29055 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e29056 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e29057 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b29058 := hb (x (-5) 7)
                  have b29059 := hb (x (-4) 6)
                  have b29060 := hb (x (-3) 5)
                  have b29061 := hb (x (-2) 4)
                  have b29062 := hb (x (-1) 11)
                  have b29063 := hb (x 0 10)
                  have b29064 := hb (x 1 9)
                  have b29065 := hb (x 2 8)
                  clear * - r29051 e29052 e29053 e29054 e29055 e29056 e29057 b29058 b29059 b29060 b29061 b29062 b29063 b29064 b29065 d29018 d29034 f28897 d28679 d28953 d28921
                  omega
                have d29066 : (x (-5) 7).toNat = 0 := by
                  have r29067 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29068 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e29069 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e29070 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e29071 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e29072 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e29073 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b29074 := hb (x (-5) 7)
                  have b29075 := hb (x (-4) 6)
                  have b29076 := hb (x (-3) 5)
                  have b29077 := hb (x (-2) 4)
                  have b29078 := hb (x (-1) 11)
                  have b29079 := hb (x 0 10)
                  have b29080 := hb (x 1 9)
                  have b29081 := hb (x 2 8)
                  clear * - r29067 e29068 e29069 e29070 e29071 e29072 e29073 b29074 b29075 b29076 b29077 b29078 b29079 b29080 b29081 d29018 d29034 f28897 d28679 d28953 d28921 d29050
                  omega
                have d29082 : (x (-5) 7 && x (-5) 12).toNat = 0 := by
                  have r29083 := hand1 (x (-5) 7) (x (-5) 12)
                  have b29084 := hb (x (-5) 7)
                  have b29085 := hb (x (-5) 7 && x (-5) 12)
                  clear * - r29083 b29084 b29085 d29066
                  omega
                have d29086 : (x (-6) 8).toNat = 0 := by
                  have r29087 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29088 := hb (x (-12) 14)
                  have b29089 := hb (x (-11) 13)
                  have b29090 := hb (x (-10) 12)
                  have b29091 := hb (x (-9) 11)
                  have b29092 := hb (x (-8) 10)
                  have b29093 := hb (x (-7) 9)
                  have b29094 := hb (x (-6) 8)
                  have b29095 := hb (x (-5) 7)
                  have b29096 := hb (x (-4) 6)
                  have b29097 := hb (x (-3) 5)
                  have b29098 := hb (x (-2) 4)
                  have b29099 := hb (x (-1) 3)
                  have b29100 := hb (x 0 2)
                  have b29101 := hb (x 1 1)
                  clear * - r29087 b29088 b29089 b29090 b29091 b29092 b29093 b29094 b29095 b29096 b29097 b29098 b29099 b29100 b29101 g2 f28586 d28663 d28953 d28921 d29050 d29066
                  omega
                have d29102 : (x (-6) 8 && x (-6) 13).toNat = 0 := by
                  have r29103 := hand1 (x (-6) 8) (x (-6) 13)
                  have b29104 := hb (x (-6) 8)
                  have b29105 := hb (x (-6) 8 && x (-6) 13)
                  clear * - r29103 b29104 b29105 d29086
                  omega
                have d29106 : (x (-7) 9).toNat = 0 := by
                  have r29107 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29108 := hb (x (-12) 14)
                  have b29109 := hb (x (-11) 13)
                  have b29110 := hb (x (-10) 12)
                  have b29111 := hb (x (-9) 11)
                  have b29112 := hb (x (-8) 10)
                  have b29113 := hb (x (-7) 9)
                  have b29114 := hb (x (-6) 8)
                  have b29115 := hb (x (-5) 7)
                  have b29116 := hb (x (-4) 6)
                  have b29117 := hb (x (-3) 5)
                  have b29118 := hb (x (-2) 4)
                  have b29119 := hb (x (-1) 3)
                  have b29120 := hb (x 0 2)
                  have b29121 := hb (x 1 1)
                  clear * - r29107 b29108 b29109 b29110 b29111 b29112 b29113 b29114 b29115 b29116 b29117 b29118 b29119 b29120 b29121 g2 f28586 d28663 d28953 d28921 d29050 d29066 d29086
                  omega
                have d29122 : (x (-7) 9 && x (-7) 14).toNat = 0 := by
                  have r29123 := hand1 (x (-7) 9) (x (-7) 14)
                  have b29124 := hb (x (-7) 9)
                  have b29125 := hb (x (-7) 9 && x (-7) 14)
                  clear * - r29123 b29124 b29125 d29106
                  omega
                have d29126 : (x (-8) 10).toNat = 0 := by
                  have r29127 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29128 := hb (x (-12) 14)
                  have b29129 := hb (x (-11) 13)
                  have b29130 := hb (x (-10) 12)
                  have b29131 := hb (x (-9) 11)
                  have b29132 := hb (x (-8) 10)
                  have b29133 := hb (x (-7) 9)
                  have b29134 := hb (x (-6) 8)
                  have b29135 := hb (x (-5) 7)
                  have b29136 := hb (x (-4) 6)
                  have b29137 := hb (x (-3) 5)
                  have b29138 := hb (x (-2) 4)
                  have b29139 := hb (x (-1) 3)
                  have b29140 := hb (x 0 2)
                  have b29141 := hb (x 1 1)
                  clear * - r29127 b29128 b29129 b29130 b29131 b29132 b29133 b29134 b29135 b29136 b29137 b29138 b29139 b29140 b29141 g2 f28586 d28663 d28953 d28921 d29050 d29066 d29086 d29106
                  omega
                have d29142 : (x (-8) 1 && x (-8) 10).toNat = 0 := by
                  have r29143 := hand2 (x (-8) 1) (x (-8) 10)
                  have b29144 := hb (x (-8) 10)
                  have b29145 := hb (x (-8) 1 && x (-8) 10)
                  clear * - r29143 b29144 b29145 d29126
                  omega
                have d29146 : (x (-2) 4 && x (-2) 9).toNat = 1 := by
                  have r29147 : 1 ≤ (x 2 5).toNat + (x 1 1 && x 1 6).toNat + (x 0 2 && x 0 7).toNat + (x (-1) 3 && x (-1) 8).toNat + (x (-2) 4 && x (-2) 9).toNat + (x (-3) 5 && x (-3) 10).toNat + (x (-4) 6 && x (-4) 11).toNat + (x (-5) 7 && x (-5) 12).toNat + (x (-6) 8 && x (-6) 13).toNat + (x (-7) 9 && x (-7) 14).toNat + (x (-8) 10).toNat := by have q := hcov5 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29148 := hb (x (-8) 10)
                  have b29149 := hb (x 2 5)
                  have b29150 := hb (x 1 1 && x 1 6)
                  have b29151 := hb (x 0 2 && x 0 7)
                  have b29152 := hb (x (-1) 3 && x (-1) 8)
                  have b29153 := hb (x (-2) 4 && x (-2) 9)
                  have b29154 := hb (x (-3) 5 && x (-3) 10)
                  have b29155 := hb (x (-4) 6 && x (-4) 11)
                  have b29156 := hb (x (-5) 7 && x (-5) 12)
                  have b29157 := hb (x (-6) 8 && x (-6) 13)
                  have b29158 := hb (x (-7) 9 && x (-7) 14)
                  clear * - r29147 b29148 b29149 b29150 b29151 b29152 b29153 b29154 b29155 b29156 b29157 b29158 d28764 g19 d28890 d28671 d28925 d29014 d29082 d29102 d29122 d29126
                  omega
                have d29159 : (x (-2) 9).toNat = 1 := by
                  have r29160 := hand2 (x (-2) 4) (x (-2) 9)
                  have b29161 := hb (x (-2) 9)
                  have b29162 := hb (x (-2) 4 && x (-2) 9)
                  clear * - r29160 b29161 b29162 d29146
                  omega
                have d29163 : (x (-1) 8).toNat = 0 := by
                  have r29164 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29165 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e29166 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e29167 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e29168 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e29169 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e29170 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b29171 := hb (x (-8) 7)
                  have b29172 := hb (x (-7) 6)
                  have b29173 := hb (x (-6) 5)
                  have b29174 := hb (x (-5) 4)
                  have b29175 := hb (x (-4) 11)
                  have b29176 := hb (x (-3) 10)
                  have b29177 := hb (x (-2) 9)
                  have b29178 := hb (x (-1) 8)
                  clear * - r29164 e29165 e29166 e29167 e29168 e29169 e29170 b29171 b29172 b29173 b29174 b29175 b29176 b29177 b29178 d29159 d28994 d29010
                  omega
                have d29179 : (x (-5) 4).toNat = 0 := by
                  have r29180 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29181 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e29182 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e29183 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e29184 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e29185 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e29186 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b29187 := hb (x (-8) 7)
                  have b29188 := hb (x (-7) 6)
                  have b29189 := hb (x (-6) 5)
                  have b29190 := hb (x (-5) 4)
                  have b29191 := hb (x (-4) 11)
                  have b29192 := hb (x (-3) 10)
                  have b29193 := hb (x (-2) 9)
                  have b29194 := hb (x (-1) 8)
                  clear * - r29180 e29181 e29182 e29183 e29184 e29185 e29186 b29187 b29188 b29189 b29190 b29191 b29192 b29193 b29194 d29163 d29159 d28994 d29010
                  omega
                have d29195 : (x (-5) 4 && x (-5) 13).toNat = 0 := by
                  have r29196 := hand1 (x (-5) 4) (x (-5) 13)
                  have b29197 := hb (x (-5) 4)
                  have b29198 := hb (x (-5) 4 && x (-5) 13)
                  clear * - r29196 b29197 b29198 d29179
                  omega
                have d29199 : (x (-6) 5).toNat = 0 := by
                  have r29200 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29201 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e29202 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e29203 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e29204 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e29205 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e29206 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b29207 := hb (x (-8) 7)
                  have b29208 := hb (x (-7) 6)
                  have b29209 := hb (x (-6) 5)
                  have b29210 := hb (x (-5) 4)
                  have b29211 := hb (x (-4) 11)
                  have b29212 := hb (x (-3) 10)
                  have b29213 := hb (x (-2) 9)
                  have b29214 := hb (x (-1) 8)
                  clear * - r29200 e29201 e29202 e29203 e29204 e29205 e29206 b29207 b29208 b29209 b29210 b29211 b29212 b29213 b29214 d29163 d29159 d28994 d29010 d29179
                  omega
                have d29215 : (x (-6) 5 && x (-6) 14).toNat = 0 := by
                  have r29216 := hand1 (x (-6) 5) (x (-6) 14)
                  have b29217 := hb (x (-6) 5)
                  have b29218 := hb (x (-6) 5 && x (-6) 14)
                  clear * - r29216 b29217 b29218 d29199
                  omega
                have d29219 : (x (-7) 6).toNat = 0 := by
                  have r29220 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29221 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e29222 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e29223 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e29224 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e29225 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e29226 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b29227 := hb (x (-8) 7)
                  have b29228 := hb (x (-7) 6)
                  have b29229 := hb (x (-6) 5)
                  have b29230 := hb (x (-5) 4)
                  have b29231 := hb (x (-4) 11)
                  have b29232 := hb (x (-3) 10)
                  have b29233 := hb (x (-2) 9)
                  have b29234 := hb (x (-1) 8)
                  clear * - r29220 e29221 e29222 e29223 e29224 e29225 e29226 b29227 b29228 b29229 b29230 b29231 b29232 b29233 b29234 d29163 d29159 d28994 d29010 d29179 d29199
                  omega
                have d29235 : (x (-2) 1 && x (-2) 10).toNat = 1 := by
                  have r29236 : 1 ≤ (x (-1) 9).toNat + (x (-2) 1 && x (-2) 10).toNat + (x (-3) 2 && x (-3) 11).toNat + (x (-4) 3 && x (-4) 12).toNat + (x (-5) 4 && x (-5) 13).toNat + (x (-6) 5 && x (-6) 14).toNat + (x (-7) 6).toNat := by have q := hcov9 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29237 := hb (x (-7) 6)
                  have b29238 := hb (x (-1) 9)
                  have b29239 := hb (x (-2) 1 && x (-2) 10)
                  have b29240 := hb (x (-3) 2 && x (-3) 11)
                  have b29241 := hb (x (-4) 3 && x (-4) 12)
                  have b29242 := hb (x (-5) 4 && x (-5) 13)
                  have b29243 := hb (x (-6) 5 && x (-6) 14)
                  clear * - r29236 b29237 b29238 b29239 b29240 b29241 b29242 b29243 d28623 d28941 d29006 d29195 d29215 d29219
                  omega
                have d29244 : (x (-2) 10).toNat = 1 := by
                  have r29245 := hand2 (x (-2) 1) (x (-2) 10)
                  have b29246 := hb (x (-2) 10)
                  have b29247 := hb (x (-2) 1 && x (-2) 10)
                  clear * - r29245 b29246 b29247 d29235
                  omega
                have d29248 : (x (-4) 4).toNat = 0 := by
                  have r29249 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29250 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                  have e29251 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                  have e29252 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                  have e29253 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                  have e29254 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                  have e29255 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                  have b29256 := hb (x (-7) 7)
                  have b29257 := hb (x (-6) 6)
                  have b29258 := hb (x (-5) 5)
                  have b29259 := hb (x (-4) 4)
                  have b29260 := hb (x (-3) 11)
                  have b29261 := hb (x (-2) 10)
                  have b29262 := hb (x (-1) 9)
                  have b29263 := hb (x 0 8)
                  clear * - r29249 e29250 e29251 e29252 e29253 e29254 e29255 b29256 b29257 b29258 b29259 b29260 b29261 b29262 b29263 f28895 d28623 d29244 d28937
                  omega
                have d29264 : (x (-5) 5).toNat = 0 := by
                  have r29265 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29266 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                  have e29267 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                  have e29268 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                  have e29269 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                  have e29270 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                  have e29271 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                  have b29272 := hb (x (-7) 7)
                  have b29273 := hb (x (-6) 6)
                  have b29274 := hb (x (-5) 5)
                  have b29275 := hb (x (-4) 4)
                  have b29276 := hb (x (-3) 11)
                  have b29277 := hb (x (-2) 10)
                  have b29278 := hb (x (-1) 9)
                  have b29279 := hb (x 0 8)
                  clear * - r29265 e29266 e29267 e29268 e29269 e29270 e29271 b29272 b29273 b29274 b29275 b29276 b29277 b29278 b29279 f28895 d28623 d29244 d28937 d29248
                  omega
                have d29280 : (x (-6) 6).toNat = 0 := by
                  have r29281 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29282 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                  have e29283 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                  have e29284 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                  have e29285 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                  have e29286 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                  have e29287 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                  have b29288 := hb (x (-7) 7)
                  have b29289 := hb (x (-6) 6)
                  have b29290 := hb (x (-5) 5)
                  have b29291 := hb (x (-4) 4)
                  have b29292 := hb (x (-3) 11)
                  have b29293 := hb (x (-2) 10)
                  have b29294 := hb (x (-1) 9)
                  have b29295 := hb (x 0 8)
                  clear * - r29281 e29282 e29283 e29284 e29285 e29286 e29287 b29288 b29289 b29290 b29291 b29292 b29293 b29294 b29295 f28895 d28623 d29244 d28937 d29248 d29264
                  omega
                have d29296 : (x (-6) 1 && x (-6) 6).toNat = 0 := by
                  have r29297 := hand2 (x (-6) 1) (x (-6) 6)
                  have b29298 := hb (x (-6) 6)
                  have b29299 := hb (x (-6) 1 && x (-6) 6)
                  clear * - r29297 b29298 b29299 d29280
                  omega
                have d29300 : (x (-7) 7).toNat = 0 := by
                  have r29301 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29302 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
                  have e29303 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
                  have e29304 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
                  have e29305 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
                  have e29306 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
                  have e29307 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
                  have b29308 := hb (x (-7) 7)
                  have b29309 := hb (x (-6) 6)
                  have b29310 := hb (x (-5) 5)
                  have b29311 := hb (x (-4) 4)
                  have b29312 := hb (x (-3) 11)
                  have b29313 := hb (x (-2) 10)
                  have b29314 := hb (x (-1) 9)
                  have b29315 := hb (x 0 8)
                  clear * - r29301 e29302 e29303 e29304 e29305 e29306 e29307 b29308 b29309 b29310 b29311 b29312 b29313 b29314 b29315 f28895 d28623 d29244 d28937 d29248 d29264 d29280
                  omega
                have d29316 : (x (-7) 2 && x (-7) 7).toNat = 0 := by
                  have r29317 := hand2 (x (-7) 2) (x (-7) 7)
                  have b29318 := hb (x (-7) 7)
                  have b29319 := hb (x (-7) 2 && x (-7) 7)
                  clear * - r29317 b29318 b29319 d29300
                  omega
                have d29320 : (x (-8) 7).toNat = 0 := by
                  have r29321 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29322 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
                  have e29323 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
                  have e29324 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
                  have e29325 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
                  have e29326 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
                  have e29327 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
                  have b29328 := hb (x (-8) 7)
                  have b29329 := hb (x (-7) 6)
                  have b29330 := hb (x (-6) 5)
                  have b29331 := hb (x (-5) 4)
                  have b29332 := hb (x (-4) 11)
                  have b29333 := hb (x (-3) 10)
                  have b29334 := hb (x (-2) 9)
                  have b29335 := hb (x (-1) 8)
                  clear * - r29321 e29322 e29323 e29324 e29325 e29326 e29327 b29328 b29329 b29330 b29331 b29332 b29333 b29334 b29335 d29163 d29159 d28994 d29010 d29179 d29199 d29219
                  omega
                have d29336 : (x (-9) 11).toNat = 0 := by
                  have r29337 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29338 := hb (x (-12) 14)
                  have b29339 := hb (x (-11) 13)
                  have b29340 := hb (x (-10) 12)
                  have b29341 := hb (x (-9) 11)
                  have b29342 := hb (x (-8) 10)
                  have b29343 := hb (x (-7) 9)
                  have b29344 := hb (x (-6) 8)
                  have b29345 := hb (x (-5) 7)
                  have b29346 := hb (x (-4) 6)
                  have b29347 := hb (x (-3) 5)
                  have b29348 := hb (x (-2) 4)
                  have b29349 := hb (x (-1) 3)
                  have b29350 := hb (x 0 2)
                  have b29351 := hb (x 1 1)
                  clear * - r29337 b29338 b29339 b29340 b29341 b29342 b29343 b29344 b29345 b29346 b29347 b29348 b29349 b29350 b29351 g2 f28586 d28663 d28953 d28921 d29050 d29066 d29086 d29106 d29126
                  omega
                have d29352 : (x (-9) 1 && x (-9) 11).toNat = 0 := by
                  have r29353 := hand2 (x (-9) 1) (x (-9) 11)
                  have b29354 := hb (x (-9) 11)
                  have b29355 := hb (x (-9) 1 && x (-9) 11)
                  clear * - r29353 b29354 b29355 d29336
                  omega
                have d29356 : (x (-9) 2 && x (-9) 11).toNat = 0 := by
                  have r29357 := hand2 (x (-9) 2) (x (-9) 11)
                  have b29358 := hb (x (-9) 11)
                  have b29359 := hb (x (-9) 2 && x (-9) 11)
                  clear * - r29357 b29358 b29359 d29336
                  omega
                have d29360 : (x (-10) 12).toNat = 0 := by
                  have r29361 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29362 := hb (x (-12) 14)
                  have b29363 := hb (x (-11) 13)
                  have b29364 := hb (x (-10) 12)
                  have b29365 := hb (x (-9) 11)
                  have b29366 := hb (x (-8) 10)
                  have b29367 := hb (x (-7) 9)
                  have b29368 := hb (x (-6) 8)
                  have b29369 := hb (x (-5) 7)
                  have b29370 := hb (x (-4) 6)
                  have b29371 := hb (x (-3) 5)
                  have b29372 := hb (x (-2) 4)
                  have b29373 := hb (x (-1) 3)
                  have b29374 := hb (x 0 2)
                  have b29375 := hb (x 1 1)
                  clear * - r29361 b29362 b29363 b29364 b29365 b29366 b29367 b29368 b29369 b29370 b29371 b29372 b29373 b29374 b29375 g2 f28586 d28663 d28953 d28921 d29050 d29066 d29086 d29106 d29126 d29336
                  omega
                have d29376 : (x (-10) 2 && x (-10) 12).toNat = 0 := by
                  have r29377 := hand2 (x (-10) 2) (x (-10) 12)
                  have b29378 := hb (x (-10) 12)
                  have b29379 := hb (x (-10) 2 && x (-10) 12)
                  clear * - r29377 b29378 b29379 d29360
                  omega
                have d29380 : (x (-10) 3 && x (-10) 12).toNat = 0 := by
                  have r29381 := hand2 (x (-10) 3) (x (-10) 12)
                  have b29382 := hb (x (-10) 12)
                  have b29383 := hb (x (-10) 3 && x (-10) 12)
                  clear * - r29381 b29382 b29383 d29360
                  omega
                have d29384 : (x (-11) 13).toNat = 0 := by
                  have r29385 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29386 := hb (x (-12) 14)
                  have b29387 := hb (x (-11) 13)
                  have b29388 := hb (x (-10) 12)
                  have b29389 := hb (x (-9) 11)
                  have b29390 := hb (x (-8) 10)
                  have b29391 := hb (x (-7) 9)
                  have b29392 := hb (x (-6) 8)
                  have b29393 := hb (x (-5) 7)
                  have b29394 := hb (x (-4) 6)
                  have b29395 := hb (x (-3) 5)
                  have b29396 := hb (x (-2) 4)
                  have b29397 := hb (x (-1) 3)
                  have b29398 := hb (x 0 2)
                  have b29399 := hb (x 1 1)
                  clear * - r29385 b29386 b29387 b29388 b29389 b29390 b29391 b29392 b29393 b29394 b29395 b29396 b29397 b29398 b29399 g2 f28586 d28663 d28953 d28921 d29050 d29066 d29086 d29106 d29126 d29336 d29360
                  omega
                have d29400 : (x (-11) 3 && x (-11) 13).toNat = 0 := by
                  have r29401 := hand2 (x (-11) 3) (x (-11) 13)
                  have b29402 := hb (x (-11) 13)
                  have b29403 := hb (x (-11) 3 && x (-11) 13)
                  clear * - r29401 b29402 b29403 d29384
                  omega
                have d29404 : (x (-11) 4 && x (-11) 13).toNat = 0 := by
                  have r29405 := hand2 (x (-11) 4) (x (-11) 13)
                  have b29406 := hb (x (-11) 13)
                  have b29407 := hb (x (-11) 4 && x (-11) 13)
                  clear * - r29405 b29406 b29407 d29384
                  omega
                have d29408 : (x (-12) 14).toNat = 0 := by
                  have r29409 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29410 := hb (x (-12) 14)
                  have b29411 := hb (x (-11) 13)
                  have b29412 := hb (x (-10) 12)
                  have b29413 := hb (x (-9) 11)
                  have b29414 := hb (x (-8) 10)
                  have b29415 := hb (x (-7) 9)
                  have b29416 := hb (x (-6) 8)
                  have b29417 := hb (x (-5) 7)
                  have b29418 := hb (x (-4) 6)
                  have b29419 := hb (x (-3) 5)
                  have b29420 := hb (x (-2) 4)
                  have b29421 := hb (x (-1) 3)
                  have b29422 := hb (x 0 2)
                  have b29423 := hb (x 1 1)
                  clear * - r29409 b29410 b29411 b29412 b29413 b29414 b29415 b29416 b29417 b29418 b29419 b29420 b29421 b29422 b29423 g2 f28586 d28663 d28953 d28921 d29050 d29066 d29086 d29106 d29126 d29336 d29360 d29384
                  omega
                have d29424 : (x (-12) 1 && x (-12) 14).toNat = 0 := by
                  have r29425 := hand2 (x (-12) 1) (x (-12) 14)
                  have b29426 := hb (x (-12) 14)
                  have b29427 := hb (x (-12) 1 && x (-12) 14)
                  clear * - r29425 b29426 b29427 d29408
                  omega
                have d29428 : (x (-13) 2).toNat = 1 := by
                  have r29429 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := by have q := hcov13 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29430 := hb (x (-13) 2)
                  have b29431 := hb (x (-11) 13)
                  have b29432 := hb (x (-12) 1 && x (-12) 14)
                  clear * - r29429 b29430 b29431 b29432 d29384 d29424
                  omega
                have d29433 : (x (-13) 14).toNat = 1 := by
                  have r29434 : (x (-13) 2).toNat ≤ (x (-13) 14).toNat := himp _ _ (hp2 (-13))
                  have b29435 := hb (x (-13) 2)
                  have b29436 := hb (x (-13) 14)
                  clear * - r29434 b29435 b29436 d29428
                  omega
                have d29437 : (x (-14) 1).toNat = 0 := by
                  have r29438 : (x (-13) 14).toNat + (x (-14) 1).toNat = 1 := by have q := hd14 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29439 := hb (x (-14) 1)
                  have b29440 := hb (x (-13) 14)
                  clear * - r29438 b29439 b29440 d29433
                  omega
                have d29441 : (x (-14) 1 && x (-14) 14).toNat = 0 := by
                  have r29442 := hand1 (x (-14) 1) (x (-14) 14)
                  have b29443 := hb (x (-14) 1)
                  have b29444 := hb (x (-14) 1 && x (-14) 14)
                  clear * - r29442 b29443 b29444 d29437
                  omega
                have d29445 : (x (-14) 1 && x (-14) 11).toNat = 0 := by
                  have r29446 := hand1 (x (-14) 1) (x (-14) 11)
                  have b29447 := hb (x (-14) 1)
                  have b29448 := hb (x (-14) 1 && x (-14) 11)
                  clear * - r29446 b29447 b29448 d29437
                  omega
                have d29449 : (x (-14) 13).toNat = 0 := by
                  have r29450 : (x (-14) 13).toNat ≤ (x (-14) 1).toNat := himp _ _ (hp13 (-14))
                  have b29451 := hb (x (-14) 1)
                  have b29452 := hb (x (-14) 13)
                  clear * - r29450 b29451 b29452 d29437
                  omega
                have d29453 : (x (-14) 5).toNat = 0 := by
                  have r29454 : (x (-14) 5).toNat ≤ (x (-14) 13).toNat := himp _ _ (hp5 (-14))
                  have b29455 := hb (x (-14) 5)
                  have b29456 := hb (x (-14) 13)
                  clear * - r29454 b29455 b29456 d29449
                  omega
                have d29457 : (x (-14) 9).toNat = 0 := by
                  have r29458 : (x (-14) 9).toNat ≤ (x (-14) 1).toNat := himp _ _ (hp9 (-14))
                  have b29459 := hb (x (-14) 1)
                  have b29460 := hb (x (-14) 9)
                  clear * - r29458 b29459 b29460 d29437
                  omega
                have d29461 : (x (-14) 9 && x (-14) 14).toNat = 0 := by
                  have r29462 := hand1 (x (-14) 9) (x (-14) 14)
                  have b29463 := hb (x (-14) 9)
                  have b29464 := hb (x (-14) 9 && x (-14) 14)
                  clear * - r29462 b29463 b29464 d29457
                  omega
                have d29465 : (x (-11) 12).toNat = 0 := by
                  have r29466 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29467 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
                  have e29468 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
                  have b29469 := hb (x (-14) 3)
                  have b29470 := hb (x (-13) 2)
                  have b29471 := hb (x (-12) 13)
                  have b29472 := hb (x (-11) 12)
                  clear * - r29466 e29467 e29468 b29469 b29470 b29471 b29472 d29428
                  omega
                have d29473 : (x (-11) 2 && x (-11) 12).toNat = 0 := by
                  have r29474 := hand2 (x (-11) 2) (x (-11) 12)
                  have b29475 := hb (x (-11) 12)
                  have b29476 := hb (x (-11) 2 && x (-11) 12)
                  clear * - r29474 b29475 b29476 d29465
                  omega
                have d29477 : (x (-11) 4).toNat = 0 := by
                  have r29478 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
                  have b29479 := hb (x (-11) 4)
                  have b29480 := hb (x (-11) 12)
                  clear * - r29478 b29479 b29480 d29465
                  omega
                have d29481 : (x (-12) 13).toNat = 0 := by
                  have r29482 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := by have q := hd12 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29483 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
                  have e29484 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
                  have b29485 := hb (x (-14) 3)
                  have b29486 := hb (x (-13) 2)
                  have b29487 := hb (x (-12) 13)
                  have b29488 := hb (x (-11) 12)
                  clear * - r29482 e29483 e29484 b29485 b29486 b29487 b29488 d29465 d29428
                  omega
                have d29489 : (x (-12) 3 && x (-12) 13).toNat = 0 := by
                  have r29490 := hand2 (x (-12) 3) (x (-12) 13)
                  have b29491 := hb (x (-12) 13)
                  have b29492 := hb (x (-12) 3 && x (-12) 13)
                  clear * - r29490 b29491 b29492 d29481
                  omega
                have d29493 : (x (-12) 5).toNat = 0 := by
                  have r29494 : (x (-12) 5).toNat ≤ (x (-12) 13).toNat := himp _ _ (hp5 (-12))
                  have b29495 := hb (x (-12) 5)
                  have b29496 := hb (x (-12) 13)
                  clear * - r29494 b29495 b29496 d29481
                  omega
                have d29497 : (x (-12) 5 && x (-12) 14).toNat = 0 := by
                  have r29498 := hand1 (x (-12) 5) (x (-12) 14)
                  have b29499 := hb (x (-12) 5)
                  have b29500 := hb (x (-12) 5 && x (-12) 14)
                  clear * - r29498 b29499 b29500 d29493
                  omega
                have d29501 : (x (-13) 6).toNat = 1 := by
                  have r29502 : 1 ≤ (x (-7) 9).toNat + (x (-8) 1 && x (-8) 10).toNat + (x (-9) 2 && x (-9) 11).toNat + (x (-10) 3 && x (-10) 12).toNat + (x (-11) 4 && x (-11) 13).toNat + (x (-12) 5 && x (-12) 14).toNat + (x (-13) 6).toNat := by have q := hcov9 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29503 := hb (x (-13) 6)
                  have b29504 := hb (x (-7) 9)
                  have b29505 := hb (x (-8) 1 && x (-8) 10)
                  have b29506 := hb (x (-9) 2 && x (-9) 11)
                  have b29507 := hb (x (-10) 3 && x (-10) 12)
                  have b29508 := hb (x (-11) 4 && x (-11) 13)
                  have b29509 := hb (x (-12) 5 && x (-12) 14)
                  clear * - r29502 b29503 b29504 b29505 b29506 b29507 b29508 b29509 d29106 d29142 d29356 d29380 d29404 d29497
                  omega
                have d29510 : (x (-7) 8).toNat = 0 := by
                  have r29511 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29512 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                  have e29513 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                  have e29514 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                  have e29515 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                  have e29516 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                  have e29517 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                  have b29518 := hb (x (-14) 7)
                  have b29519 := hb (x (-13) 6)
                  have b29520 := hb (x (-12) 5)
                  have b29521 := hb (x (-11) 4)
                  have b29522 := hb (x (-10) 11)
                  have b29523 := hb (x (-9) 10)
                  have b29524 := hb (x (-8) 9)
                  have b29525 := hb (x (-7) 8)
                  clear * - r29511 e29512 e29513 e29514 e29515 e29516 e29517 b29518 b29519 b29520 b29521 b29522 b29523 b29524 b29525 d29477 d29493 d29501
                  omega
                have d29526 : (x (-8) 9).toNat = 0 := by
                  have r29527 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29528 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                  have e29529 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                  have e29530 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                  have e29531 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                  have e29532 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                  have e29533 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                  have b29534 := hb (x (-14) 7)
                  have b29535 := hb (x (-13) 6)
                  have b29536 := hb (x (-12) 5)
                  have b29537 := hb (x (-11) 4)
                  have b29538 := hb (x (-10) 11)
                  have b29539 := hb (x (-9) 10)
                  have b29540 := hb (x (-8) 9)
                  have b29541 := hb (x (-7) 8)
                  clear * - r29527 e29528 e29529 e29530 e29531 e29532 e29533 b29534 b29535 b29536 b29537 b29538 b29539 b29540 b29541 d29510 d29477 d29493 d29501
                  omega
                have d29542 : (x (-9) 10).toNat = 0 := by
                  have r29543 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29544 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                  have e29545 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                  have e29546 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                  have e29547 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                  have e29548 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                  have e29549 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                  have b29550 := hb (x (-14) 7)
                  have b29551 := hb (x (-13) 6)
                  have b29552 := hb (x (-12) 5)
                  have b29553 := hb (x (-11) 4)
                  have b29554 := hb (x (-10) 11)
                  have b29555 := hb (x (-9) 10)
                  have b29556 := hb (x (-8) 9)
                  have b29557 := hb (x (-7) 8)
                  clear * - r29543 e29544 e29545 e29546 e29547 e29548 e29549 b29550 b29551 b29552 b29553 b29554 b29555 b29556 b29557 d29510 d29526 d29477 d29493 d29501
                  omega
                have d29558 : (x (-10) 11).toNat = 0 := by
                  have r29559 : (x (-7) 8).toNat + (x (-8) 1 && x (-8) 9).toNat + (x (-9) 2 && x (-9) 10).toNat + (x (-10) 3 && x (-10) 11).toNat + (x (-11) 4 && x (-11) 12).toNat + (x (-12) 5 && x (-12) 13).toNat + (x (-13) 6 && x (-13) 14).toNat + (x (-14) 7).toNat = 1 := by have q := hd8 (-7); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29560 : (x (-8) 1 && x (-8) 9).toNat = (x (-8) 9).toNat := handr _ _ (fun h => hp9 (-8) (h))
                  have e29561 : (x (-9) 2 && x (-9) 10).toNat = (x (-9) 10).toNat := handr _ _ (fun h => hp10 (-9) (h))
                  have e29562 : (x (-10) 3 && x (-10) 11).toNat = (x (-10) 11).toNat := handr _ _ (fun h => hp11 (-10) (h))
                  have e29563 : (x (-11) 4 && x (-11) 12).toNat = (x (-11) 4).toNat := handl _ _ (fun h => hp4 (-11) (h))
                  have e29564 : (x (-12) 5 && x (-12) 13).toNat = (x (-12) 5).toNat := handl _ _ (fun h => hp5 (-12) (h))
                  have e29565 : (x (-13) 6 && x (-13) 14).toNat = (x (-13) 6).toNat := handl _ _ (fun h => hp6 (-13) (h))
                  have b29566 := hb (x (-14) 7)
                  have b29567 := hb (x (-13) 6)
                  have b29568 := hb (x (-12) 5)
                  have b29569 := hb (x (-11) 4)
                  have b29570 := hb (x (-10) 11)
                  have b29571 := hb (x (-9) 10)
                  have b29572 := hb (x (-8) 9)
                  have b29573 := hb (x (-7) 8)
                  clear * - r29559 e29560 e29561 e29562 e29563 e29564 e29565 b29566 b29567 b29568 b29569 b29570 b29571 b29572 b29573 d29510 d29526 d29542 d29477 d29493 d29501
                  omega
                have d29574 : (x (-10) 1 && x (-10) 11).toNat = 0 := by
                  have r29575 := hand2 (x (-10) 1) (x (-10) 11)
                  have b29576 := hb (x (-10) 11)
                  have b29577 := hb (x (-10) 1 && x (-10) 11)
                  clear * - r29575 b29576 b29577 d29558
                  omega
                have d29578 : (x (-13) 4 && x (-13) 14).toNat = 1 := by
                  have r29579 : 1 ≤ (x (-9) 10).toNat + (x (-10) 1 && x (-10) 11).toNat + (x (-11) 2 && x (-11) 12).toNat + (x (-12) 3 && x (-12) 13).toNat + (x (-13) 4 && x (-13) 14).toNat + (x (-14) 5).toNat := by have q := hcov10 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29580 := hb (x (-14) 5)
                  have b29581 := hb (x (-9) 10)
                  have b29582 := hb (x (-10) 1 && x (-10) 11)
                  have b29583 := hb (x (-11) 2 && x (-11) 12)
                  have b29584 := hb (x (-12) 3 && x (-12) 13)
                  have b29585 := hb (x (-13) 4 && x (-13) 14)
                  clear * - r29579 b29580 b29581 b29582 b29583 b29584 b29585 d29542 d29574 d29473 d29489 d29453
                  omega
                have d29586 : (x (-13) 4).toNat = 1 := by
                  have r29587 := hand1 (x (-13) 4) (x (-13) 14)
                  have b29588 := hb (x (-13) 4)
                  have b29589 := hb (x (-13) 4 && x (-13) 14)
                  clear * - r29587 b29588 b29589 d29578
                  omega
                have d29590 : (x (-13) 12).toNat = 1 := by
                  have r29591 : (x (-13) 4).toNat ≤ (x (-13) 12).toNat := himp _ _ (hp4 (-13))
                  have b29592 := hb (x (-13) 4)
                  have b29593 := hb (x (-13) 12)
                  clear * - r29591 b29592 b29593 d29586
                  omega
                have d29594 : (x (-15) 2).toNat = 0 := by
                  have r29595 : (x (-13) 12).toNat + (x (-14) 1 && x (-14) 13).toNat + (x (-15) 2 && x (-15) 14).toNat + (x (-16) 3).toNat = 1 := by have q := hd12 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29596 : (x (-14) 1 && x (-14) 13).toNat = (x (-14) 13).toNat := handr _ _ (fun h => hp13 (-14) (h))
                  have e29597 : (x (-15) 2 && x (-15) 14).toNat = (x (-15) 2).toNat := handl _ _ (fun h => hp2 (-15) (h))
                  have b29598 := hb (x (-16) 3)
                  have b29599 := hb (x (-15) 2)
                  have b29600 := hb (x (-14) 13)
                  have b29601 := hb (x (-13) 12)
                  clear * - r29595 e29596 e29597 b29598 b29599 b29600 b29601 d29590 d29449
                  omega
                have d29602 : (x (-15) 2 && x (-15) 12).toNat = 0 := by
                  have r29603 := hand1 (x (-15) 2) (x (-15) 12)
                  have b29604 := hb (x (-15) 2)
                  have b29605 := hb (x (-15) 2 && x (-15) 12)
                  clear * - r29603 b29604 b29605 d29594
                  omega
                have d29606 : (x (-15) 10).toNat = 0 := by
                  have r29607 : (x (-15) 10).toNat ≤ (x (-15) 2).toNat := himp _ _ (hp10 (-15))
                  have b29608 := hb (x (-15) 2)
                  have b29609 := hb (x (-15) 10)
                  clear * - r29607 b29608 b29609 d29594
                  omega
                have d29610 : (x (-15) 1 && x (-15) 10).toNat = 0 := by
                  have r29611 := hand2 (x (-15) 1) (x (-15) 10)
                  have b29612 := hb (x (-15) 10)
                  have b29613 := hb (x (-15) 1 && x (-15) 10)
                  clear * - r29611 b29612 b29613 d29606
                  omega
                have d29614 : (x (-13) 13).toNat = 1 := by
                  have r29615 : 1 ≤ (x (-13) 13).toNat + (x (-14) 1 && x (-14) 14).toNat + (x (-15) 2).toNat := by have q := hcov13 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29616 := hb (x (-15) 2)
                  have b29617 := hb (x (-13) 13)
                  have b29618 := hb (x (-14) 1 && x (-14) 14)
                  clear * - r29615 b29616 b29617 b29618 d29441 d29594
                  omega
                have d29619 : (x (-12) 12).toNat = 0 := by
                  have r29620 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := by have q := hd12 (-12); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29621 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
                  have e29622 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
                  have b29623 := hb (x (-15) 3)
                  have b29624 := hb (x (-14) 2)
                  have b29625 := hb (x (-13) 13)
                  have b29626 := hb (x (-12) 12)
                  clear * - r29620 e29621 e29622 b29623 b29624 b29625 b29626 d29614
                  omega
                have d29627 : (x (-12) 7 && x (-12) 12).toNat = 0 := by
                  have r29628 := hand2 (x (-12) 7) (x (-12) 12)
                  have b29629 := hb (x (-12) 12)
                  have b29630 := hb (x (-12) 7 && x (-12) 12)
                  clear * - r29628 b29629 b29630 d29619
                  omega
                have d29631 : (x (-12) 4).toNat = 0 := by
                  have r29632 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
                  have b29633 := hb (x (-12) 4)
                  have b29634 := hb (x (-12) 12)
                  clear * - r29632 b29633 b29634 d29619
                  omega
                have d29635 : (x (-12) 4 && x (-12) 14).toNat = 0 := by
                  have r29636 := hand1 (x (-12) 4) (x (-12) 14)
                  have b29637 := hb (x (-12) 4)
                  have b29638 := hb (x (-12) 4 && x (-12) 14)
                  clear * - r29636 b29637 b29638 d29631
                  omega
                have d29639 : (x (-13) 5).toNat = 1 := by
                  have r29640 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := by have q := hcov10 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29641 := hb (x (-13) 5)
                  have b29642 := hb (x (-8) 10)
                  have b29643 := hb (x (-9) 1 && x (-9) 11)
                  have b29644 := hb (x (-10) 2 && x (-10) 12)
                  have b29645 := hb (x (-11) 3 && x (-11) 13)
                  have b29646 := hb (x (-12) 4 && x (-12) 14)
                  clear * - r29640 b29641 b29642 b29643 b29644 b29645 b29646 d29126 d29352 d29376 d29400 d29635
                  omega
                have d29647 : (x (-8) 8).toNat = 0 := by
                  have r29648 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29649 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                  have e29650 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                  have e29651 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                  have e29652 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                  have e29653 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                  have e29654 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                  have b29655 := hb (x (-15) 7)
                  have b29656 := hb (x (-14) 6)
                  have b29657 := hb (x (-13) 5)
                  have b29658 := hb (x (-12) 4)
                  have b29659 := hb (x (-11) 11)
                  have b29660 := hb (x (-10) 10)
                  have b29661 := hb (x (-9) 9)
                  have b29662 := hb (x (-8) 8)
                  clear * - r29648 e29649 e29650 e29651 e29652 e29653 e29654 b29655 b29656 b29657 b29658 b29659 b29660 b29661 b29662 d29631 d29639
                  omega
                have d29663 : (x (-8) 3 && x (-8) 8).toNat = 0 := by
                  have r29664 := hand2 (x (-8) 3) (x (-8) 8)
                  have b29665 := hb (x (-8) 8)
                  have b29666 := hb (x (-8) 3 && x (-8) 8)
                  clear * - r29664 b29665 b29666 d29647
                  omega
                have d29667 : (x (-9) 9).toNat = 0 := by
                  have r29668 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29669 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                  have e29670 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                  have e29671 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                  have e29672 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                  have e29673 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                  have e29674 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                  have b29675 := hb (x (-15) 7)
                  have b29676 := hb (x (-14) 6)
                  have b29677 := hb (x (-13) 5)
                  have b29678 := hb (x (-12) 4)
                  have b29679 := hb (x (-11) 11)
                  have b29680 := hb (x (-10) 10)
                  have b29681 := hb (x (-9) 9)
                  have b29682 := hb (x (-8) 8)
                  clear * - r29668 e29669 e29670 e29671 e29672 e29673 e29674 b29675 b29676 b29677 b29678 b29679 b29680 b29681 b29682 d29647 d29631 d29639
                  omega
                have d29683 : (x (-9) 4 && x (-9) 9).toNat = 0 := by
                  have r29684 := hand2 (x (-9) 4) (x (-9) 9)
                  have b29685 := hb (x (-9) 9)
                  have b29686 := hb (x (-9) 4 && x (-9) 9)
                  clear * - r29684 b29685 b29686 d29667
                  omega
                have d29687 : (x (-10) 10).toNat = 0 := by
                  have r29688 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29689 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                  have e29690 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                  have e29691 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                  have e29692 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                  have e29693 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                  have e29694 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                  have b29695 := hb (x (-15) 7)
                  have b29696 := hb (x (-14) 6)
                  have b29697 := hb (x (-13) 5)
                  have b29698 := hb (x (-12) 4)
                  have b29699 := hb (x (-11) 11)
                  have b29700 := hb (x (-10) 10)
                  have b29701 := hb (x (-9) 9)
                  have b29702 := hb (x (-8) 8)
                  clear * - r29688 e29689 e29690 e29691 e29692 e29693 e29694 b29695 b29696 b29697 b29698 b29699 b29700 b29701 b29702 d29647 d29667 d29631 d29639
                  omega
                have d29703 : (x (-10) 5 && x (-10) 10).toNat = 0 := by
                  have r29704 := hand2 (x (-10) 5) (x (-10) 10)
                  have b29705 := hb (x (-10) 10)
                  have b29706 := hb (x (-10) 5 && x (-10) 10)
                  clear * - r29704 b29705 b29706 d29687
                  omega
                have d29707 : (x (-11) 11).toNat = 0 := by
                  have r29708 : (x (-8) 8).toNat + (x (-9) 1 && x (-9) 9).toNat + (x (-10) 2 && x (-10) 10).toNat + (x (-11) 3 && x (-11) 11).toNat + (x (-12) 4 && x (-12) 12).toNat + (x (-13) 5 && x (-13) 13).toNat + (x (-14) 6 && x (-14) 14).toNat + (x (-15) 7).toNat = 1 := by have q := hd8 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29709 : (x (-9) 1 && x (-9) 9).toNat = (x (-9) 9).toNat := handr _ _ (fun h => hp9 (-9) (h))
                  have e29710 : (x (-10) 2 && x (-10) 10).toNat = (x (-10) 10).toNat := handr _ _ (fun h => hp10 (-10) (h))
                  have e29711 : (x (-11) 3 && x (-11) 11).toNat = (x (-11) 11).toNat := handr _ _ (fun h => hp11 (-11) (h))
                  have e29712 : (x (-12) 4 && x (-12) 12).toNat = (x (-12) 4).toNat := handl _ _ (fun h => hp4 (-12) (h))
                  have e29713 : (x (-13) 5 && x (-13) 13).toNat = (x (-13) 5).toNat := handl _ _ (fun h => hp5 (-13) (h))
                  have e29714 : (x (-14) 6 && x (-14) 14).toNat = (x (-14) 6).toNat := handl _ _ (fun h => hp6 (-14) (h))
                  have b29715 := hb (x (-15) 7)
                  have b29716 := hb (x (-14) 6)
                  have b29717 := hb (x (-13) 5)
                  have b29718 := hb (x (-12) 4)
                  have b29719 := hb (x (-11) 11)
                  have b29720 := hb (x (-10) 10)
                  have b29721 := hb (x (-9) 9)
                  have b29722 := hb (x (-8) 8)
                  clear * - r29708 e29709 e29710 e29711 e29712 e29713 e29714 b29715 b29716 b29717 b29718 b29719 b29720 b29721 b29722 d29647 d29667 d29687 d29631 d29639
                  omega
                have d29723 : (x (-11) 6 && x (-11) 11).toNat = 0 := by
                  have r29724 := hand2 (x (-11) 6) (x (-11) 11)
                  have b29725 := hb (x (-11) 11)
                  have b29726 := hb (x (-11) 6 && x (-11) 11)
                  clear * - r29724 b29725 b29726 d29707
                  omega
                have d29727 : (x (-13) 8 && x (-13) 13).toNat = 1 := by
                  have r29728 : 1 ≤ (x (-5) 5).toNat + (x (-6) 1 && x (-6) 6).toNat + (x (-7) 2 && x (-7) 7).toNat + (x (-8) 3 && x (-8) 8).toNat + (x (-9) 4 && x (-9) 9).toNat + (x (-10) 5 && x (-10) 10).toNat + (x (-11) 6 && x (-11) 11).toNat + (x (-12) 7 && x (-12) 12).toNat + (x (-13) 8 && x (-13) 13).toNat + (x (-14) 9 && x (-14) 14).toNat + (x (-15) 10).toNat := by have q := hcov5 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29729 := hb (x (-15) 10)
                  have b29730 := hb (x (-5) 5)
                  have b29731 := hb (x (-6) 1 && x (-6) 6)
                  have b29732 := hb (x (-7) 2 && x (-7) 7)
                  have b29733 := hb (x (-8) 3 && x (-8) 8)
                  have b29734 := hb (x (-9) 4 && x (-9) 9)
                  have b29735 := hb (x (-10) 5 && x (-10) 10)
                  have b29736 := hb (x (-11) 6 && x (-11) 11)
                  have b29737 := hb (x (-12) 7 && x (-12) 12)
                  have b29738 := hb (x (-13) 8 && x (-13) 13)
                  have b29739 := hb (x (-14) 9 && x (-14) 14)
                  clear * - r29728 b29729 b29730 b29731 b29732 b29733 b29734 b29735 b29736 b29737 b29738 b29739 d29264 d29296 d29316 d29663 d29683 d29703 d29723 d29627 d29461 d29606
                  omega
                have d29740 : (x (-13) 8).toNat = 1 := by
                  have r29741 := hand1 (x (-13) 8) (x (-13) 13)
                  have b29742 := hb (x (-13) 8)
                  have b29743 := hb (x (-13) 8 && x (-13) 13)
                  clear * - r29741 b29742 b29743 d29727
                  omega
                have d29744 : (x (-16) 11).toNat = 0 := by
                  have r29745 : (x (-13) 8).toNat + (x (-14) 1 && x (-14) 9).toNat + (x (-15) 2 && x (-15) 10).toNat + (x (-16) 3 && x (-16) 11).toNat + (x (-17) 4 && x (-17) 12).toNat + (x (-18) 5 && x (-18) 13).toNat + (x (-19) 6 && x (-19) 14).toNat + (x (-20) 7).toNat = 1 := by have q := hd8 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29746 : (x (-14) 1 && x (-14) 9).toNat = (x (-14) 9).toNat := handr _ _ (fun h => hp9 (-14) (h))
                  have e29747 : (x (-15) 2 && x (-15) 10).toNat = (x (-15) 10).toNat := handr _ _ (fun h => hp10 (-15) (h))
                  have e29748 : (x (-16) 3 && x (-16) 11).toNat = (x (-16) 11).toNat := handr _ _ (fun h => hp11 (-16) (h))
                  have e29749 : (x (-17) 4 && x (-17) 12).toNat = (x (-17) 4).toNat := handl _ _ (fun h => hp4 (-17) (h))
                  have e29750 : (x (-18) 5 && x (-18) 13).toNat = (x (-18) 5).toNat := handl _ _ (fun h => hp5 (-18) (h))
                  have e29751 : (x (-19) 6 && x (-19) 14).toNat = (x (-19) 6).toNat := handl _ _ (fun h => hp6 (-19) (h))
                  have b29752 := hb (x (-20) 7)
                  have b29753 := hb (x (-19) 6)
                  have b29754 := hb (x (-18) 5)
                  have b29755 := hb (x (-17) 4)
                  have b29756 := hb (x (-16) 11)
                  have b29757 := hb (x (-15) 10)
                  have b29758 := hb (x (-14) 9)
                  have b29759 := hb (x (-13) 8)
                  clear * - r29745 e29746 e29747 e29748 e29749 e29750 e29751 b29752 b29753 b29754 b29755 b29756 b29757 b29758 b29759 d29740 d29457 d29606
                  omega
                have d29760 : (x (-16) 2 && x (-16) 11).toNat = 0 := by
                  have r29761 := hand2 (x (-16) 2) (x (-16) 11)
                  have b29762 := hb (x (-16) 11)
                  have b29763 := hb (x (-16) 2 && x (-16) 11)
                  clear * - r29761 b29762 b29763 d29744
                  omega
                have d29764 : (x (-17) 4).toNat = 0 := by
                  have r29765 : (x (-13) 8).toNat + (x (-14) 1 && x (-14) 9).toNat + (x (-15) 2 && x (-15) 10).toNat + (x (-16) 3 && x (-16) 11).toNat + (x (-17) 4 && x (-17) 12).toNat + (x (-18) 5 && x (-18) 13).toNat + (x (-19) 6 && x (-19) 14).toNat + (x (-20) 7).toNat = 1 := by have q := hd8 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29766 : (x (-14) 1 && x (-14) 9).toNat = (x (-14) 9).toNat := handr _ _ (fun h => hp9 (-14) (h))
                  have e29767 : (x (-15) 2 && x (-15) 10).toNat = (x (-15) 10).toNat := handr _ _ (fun h => hp10 (-15) (h))
                  have e29768 : (x (-16) 3 && x (-16) 11).toNat = (x (-16) 11).toNat := handr _ _ (fun h => hp11 (-16) (h))
                  have e29769 : (x (-17) 4 && x (-17) 12).toNat = (x (-17) 4).toNat := handl _ _ (fun h => hp4 (-17) (h))
                  have e29770 : (x (-18) 5 && x (-18) 13).toNat = (x (-18) 5).toNat := handl _ _ (fun h => hp5 (-18) (h))
                  have e29771 : (x (-19) 6 && x (-19) 14).toNat = (x (-19) 6).toNat := handl _ _ (fun h => hp6 (-19) (h))
                  have b29772 := hb (x (-20) 7)
                  have b29773 := hb (x (-19) 6)
                  have b29774 := hb (x (-18) 5)
                  have b29775 := hb (x (-17) 4)
                  have b29776 := hb (x (-16) 11)
                  have b29777 := hb (x (-15) 10)
                  have b29778 := hb (x (-14) 9)
                  have b29779 := hb (x (-13) 8)
                  clear * - r29765 e29766 e29767 e29768 e29769 e29770 e29771 b29772 b29773 b29774 b29775 b29776 b29777 b29778 b29779 d29740 d29457 d29606 d29744
                  omega
                have d29780 : (x (-17) 4 && x (-17) 14).toNat = 0 := by
                  have r29781 := hand1 (x (-17) 4) (x (-17) 14)
                  have b29782 := hb (x (-17) 4)
                  have b29783 := hb (x (-17) 4 && x (-17) 14)
                  clear * - r29781 b29782 b29783 d29764
                  omega
                have d29784 : (x (-18) 5).toNat = 0 := by
                  have r29785 : (x (-13) 8).toNat + (x (-14) 1 && x (-14) 9).toNat + (x (-15) 2 && x (-15) 10).toNat + (x (-16) 3 && x (-16) 11).toNat + (x (-17) 4 && x (-17) 12).toNat + (x (-18) 5 && x (-18) 13).toNat + (x (-19) 6 && x (-19) 14).toNat + (x (-20) 7).toNat = 1 := by have q := hd8 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29786 : (x (-14) 1 && x (-14) 9).toNat = (x (-14) 9).toNat := handr _ _ (fun h => hp9 (-14) (h))
                  have e29787 : (x (-15) 2 && x (-15) 10).toNat = (x (-15) 10).toNat := handr _ _ (fun h => hp10 (-15) (h))
                  have e29788 : (x (-16) 3 && x (-16) 11).toNat = (x (-16) 11).toNat := handr _ _ (fun h => hp11 (-16) (h))
                  have e29789 : (x (-17) 4 && x (-17) 12).toNat = (x (-17) 4).toNat := handl _ _ (fun h => hp4 (-17) (h))
                  have e29790 : (x (-18) 5 && x (-18) 13).toNat = (x (-18) 5).toNat := handl _ _ (fun h => hp5 (-18) (h))
                  have e29791 : (x (-19) 6 && x (-19) 14).toNat = (x (-19) 6).toNat := handl _ _ (fun h => hp6 (-19) (h))
                  have b29792 := hb (x (-20) 7)
                  have b29793 := hb (x (-19) 6)
                  have b29794 := hb (x (-18) 5)
                  have b29795 := hb (x (-17) 4)
                  have b29796 := hb (x (-16) 11)
                  have b29797 := hb (x (-15) 10)
                  have b29798 := hb (x (-14) 9)
                  have b29799 := hb (x (-13) 8)
                  clear * - r29785 e29786 e29787 e29788 e29789 e29790 e29791 b29792 b29793 b29794 b29795 b29796 b29797 b29798 b29799 d29740 d29457 d29606 d29744 d29764
                  omega
                have d29800 : (x (-16) 3).toNat = 0 := by
                  have r29801 : (x (-13) 12).toNat + (x (-14) 1 && x (-14) 13).toNat + (x (-15) 2 && x (-15) 14).toNat + (x (-16) 3).toNat = 1 := by have q := hd12 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29802 : (x (-14) 1 && x (-14) 13).toNat = (x (-14) 13).toNat := handr _ _ (fun h => hp13 (-14) (h))
                  have e29803 : (x (-15) 2 && x (-15) 14).toNat = (x (-15) 2).toNat := handl _ _ (fun h => hp2 (-15) (h))
                  have b29804 := hb (x (-16) 3)
                  have b29805 := hb (x (-15) 2)
                  have b29806 := hb (x (-14) 13)
                  have b29807 := hb (x (-13) 12)
                  clear * - r29801 e29802 e29803 b29804 b29805 b29806 b29807 d29590 d29449 d29594
                  omega
                have d29808 : (x (-16) 3 && x (-16) 13).toNat = 0 := by
                  have r29809 := hand1 (x (-16) 3) (x (-16) 13)
                  have b29810 := hb (x (-16) 3)
                  have b29811 := hb (x (-16) 3 && x (-16) 13)
                  clear * - r29809 b29810 b29811 d29800
                  omega
                have d29812 : (x (-13) 10).toNat = 1 := by
                  have r29813 : 1 ≤ (x (-13) 10).toNat + (x (-14) 1 && x (-14) 11).toNat + (x (-15) 2 && x (-15) 12).toNat + (x (-16) 3 && x (-16) 13).toNat + (x (-17) 4 && x (-17) 14).toNat + (x (-18) 5).toNat := by have q := hcov10 (-13); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29814 := hb (x (-18) 5)
                  have b29815 := hb (x (-13) 10)
                  have b29816 := hb (x (-14) 1 && x (-14) 11)
                  have b29817 := hb (x (-15) 2 && x (-15) 12)
                  have b29818 := hb (x (-16) 3 && x (-16) 13)
                  have b29819 := hb (x (-17) 4 && x (-17) 14)
                  clear * - r29813 b29814 b29815 b29816 b29817 b29818 b29819 d29445 d29602 d29808 d29780 d29784
                  omega
                have d29820 : (x (-11) 8).toNat = 0 := by
                  have r29821 : (x (-11) 8).toNat + (x (-12) 1 && x (-12) 9).toNat + (x (-13) 2 && x (-13) 10).toNat + (x (-14) 3 && x (-14) 11).toNat + (x (-15) 4 && x (-15) 12).toNat + (x (-16) 5 && x (-16) 13).toNat + (x (-17) 6 && x (-17) 14).toNat + (x (-18) 7).toNat = 1 := by have q := hd8 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29822 : (x (-12) 1 && x (-12) 9).toNat = (x (-12) 9).toNat := handr _ _ (fun h => hp9 (-12) (h))
                  have e29823 : (x (-13) 2 && x (-13) 10).toNat = (x (-13) 10).toNat := handr _ _ (fun h => hp10 (-13) (h))
                  have e29824 : (x (-14) 3 && x (-14) 11).toNat = (x (-14) 11).toNat := handr _ _ (fun h => hp11 (-14) (h))
                  have e29825 : (x (-15) 4 && x (-15) 12).toNat = (x (-15) 4).toNat := handl _ _ (fun h => hp4 (-15) (h))
                  have e29826 : (x (-16) 5 && x (-16) 13).toNat = (x (-16) 5).toNat := handl _ _ (fun h => hp5 (-16) (h))
                  have e29827 : (x (-17) 6 && x (-17) 14).toNat = (x (-17) 6).toNat := handl _ _ (fun h => hp6 (-17) (h))
                  have b29828 := hb (x (-18) 7)
                  have b29829 := hb (x (-17) 6)
                  have b29830 := hb (x (-16) 5)
                  have b29831 := hb (x (-15) 4)
                  have b29832 := hb (x (-14) 11)
                  have b29833 := hb (x (-13) 10)
                  have b29834 := hb (x (-12) 9)
                  have b29835 := hb (x (-11) 8)
                  clear * - r29821 e29822 e29823 e29824 e29825 e29826 e29827 b29828 b29829 b29830 b29831 b29832 b29833 b29834 b29835 d29812
                  omega
                have d29836 : (x (-12) 9).toNat = 0 := by
                  have r29837 : (x (-11) 8).toNat + (x (-12) 1 && x (-12) 9).toNat + (x (-13) 2 && x (-13) 10).toNat + (x (-14) 3 && x (-14) 11).toNat + (x (-15) 4 && x (-15) 12).toNat + (x (-16) 5 && x (-16) 13).toNat + (x (-17) 6 && x (-17) 14).toNat + (x (-18) 7).toNat = 1 := by have q := hd8 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29838 : (x (-12) 1 && x (-12) 9).toNat = (x (-12) 9).toNat := handr _ _ (fun h => hp9 (-12) (h))
                  have e29839 : (x (-13) 2 && x (-13) 10).toNat = (x (-13) 10).toNat := handr _ _ (fun h => hp10 (-13) (h))
                  have e29840 : (x (-14) 3 && x (-14) 11).toNat = (x (-14) 11).toNat := handr _ _ (fun h => hp11 (-14) (h))
                  have e29841 : (x (-15) 4 && x (-15) 12).toNat = (x (-15) 4).toNat := handl _ _ (fun h => hp4 (-15) (h))
                  have e29842 : (x (-16) 5 && x (-16) 13).toNat = (x (-16) 5).toNat := handl _ _ (fun h => hp5 (-16) (h))
                  have e29843 : (x (-17) 6 && x (-17) 14).toNat = (x (-17) 6).toNat := handl _ _ (fun h => hp6 (-17) (h))
                  have b29844 := hb (x (-18) 7)
                  have b29845 := hb (x (-17) 6)
                  have b29846 := hb (x (-16) 5)
                  have b29847 := hb (x (-15) 4)
                  have b29848 := hb (x (-14) 11)
                  have b29849 := hb (x (-13) 10)
                  have b29850 := hb (x (-12) 9)
                  have b29851 := hb (x (-11) 8)
                  clear * - r29837 e29838 e29839 e29840 e29841 e29842 e29843 b29844 b29845 b29846 b29847 b29848 b29849 b29850 b29851 d29820 d29812
                  omega
                have d29852 : (x (-14) 11).toNat = 0 := by
                  have r29853 : (x (-11) 8).toNat + (x (-12) 1 && x (-12) 9).toNat + (x (-13) 2 && x (-13) 10).toNat + (x (-14) 3 && x (-14) 11).toNat + (x (-15) 4 && x (-15) 12).toNat + (x (-16) 5 && x (-16) 13).toNat + (x (-17) 6 && x (-17) 14).toNat + (x (-18) 7).toNat = 1 := by have q := hd8 (-11); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29854 : (x (-12) 1 && x (-12) 9).toNat = (x (-12) 9).toNat := handr _ _ (fun h => hp9 (-12) (h))
                  have e29855 : (x (-13) 2 && x (-13) 10).toNat = (x (-13) 10).toNat := handr _ _ (fun h => hp10 (-13) (h))
                  have e29856 : (x (-14) 3 && x (-14) 11).toNat = (x (-14) 11).toNat := handr _ _ (fun h => hp11 (-14) (h))
                  have e29857 : (x (-15) 4 && x (-15) 12).toNat = (x (-15) 4).toNat := handl _ _ (fun h => hp4 (-15) (h))
                  have e29858 : (x (-16) 5 && x (-16) 13).toNat = (x (-16) 5).toNat := handl _ _ (fun h => hp5 (-16) (h))
                  have e29859 : (x (-17) 6 && x (-17) 14).toNat = (x (-17) 6).toNat := handl _ _ (fun h => hp6 (-17) (h))
                  have b29860 := hb (x (-18) 7)
                  have b29861 := hb (x (-17) 6)
                  have b29862 := hb (x (-16) 5)
                  have b29863 := hb (x (-15) 4)
                  have b29864 := hb (x (-14) 11)
                  have b29865 := hb (x (-13) 10)
                  have b29866 := hb (x (-12) 9)
                  have b29867 := hb (x (-11) 8)
                  clear * - r29853 e29854 e29855 e29856 e29857 e29858 e29859 b29860 b29861 b29862 b29863 b29864 b29865 b29866 b29867 d29820 d29836 d29812
                  omega
                have d29868 : (x (-9) 8).toNat = 0 := by
                  have r29869 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29870 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
                  have e29871 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
                  have e29872 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
                  have e29873 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
                  have e29874 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
                  have e29875 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
                  have b29876 := hb (x (-16) 7)
                  have b29877 := hb (x (-15) 6)
                  have b29878 := hb (x (-14) 5)
                  have b29879 := hb (x (-13) 4)
                  have b29880 := hb (x (-12) 11)
                  have b29881 := hb (x (-11) 10)
                  have b29882 := hb (x (-10) 9)
                  have b29883 := hb (x (-9) 8)
                  clear * - r29869 e29870 e29871 e29872 e29873 e29874 e29875 b29876 b29877 b29878 b29879 b29880 b29881 b29882 b29883 d29586 d29453
                  omega
                have d29884 : (x (-10) 9).toNat = 0 := by
                  have r29885 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29886 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
                  have e29887 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
                  have e29888 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
                  have e29889 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
                  have e29890 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
                  have e29891 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
                  have b29892 := hb (x (-16) 7)
                  have b29893 := hb (x (-15) 6)
                  have b29894 := hb (x (-14) 5)
                  have b29895 := hb (x (-13) 4)
                  have b29896 := hb (x (-12) 11)
                  have b29897 := hb (x (-11) 10)
                  have b29898 := hb (x (-10) 9)
                  have b29899 := hb (x (-9) 8)
                  clear * - r29885 e29886 e29887 e29888 e29889 e29890 e29891 b29892 b29893 b29894 b29895 b29896 b29897 b29898 b29899 d29868 d29586 d29453
                  omega
                have d29900 : (x (-11) 10).toNat = 0 := by
                  have r29901 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29902 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
                  have e29903 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
                  have e29904 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
                  have e29905 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
                  have e29906 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
                  have e29907 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
                  have b29908 := hb (x (-16) 7)
                  have b29909 := hb (x (-15) 6)
                  have b29910 := hb (x (-14) 5)
                  have b29911 := hb (x (-13) 4)
                  have b29912 := hb (x (-12) 11)
                  have b29913 := hb (x (-11) 10)
                  have b29914 := hb (x (-10) 9)
                  have b29915 := hb (x (-9) 8)
                  clear * - r29901 e29902 e29903 e29904 e29905 e29906 e29907 b29908 b29909 b29910 b29911 b29912 b29913 b29914 b29915 d29868 d29884 d29586 d29453
                  omega
                have d29916 : (x (-12) 11).toNat = 0 := by
                  have r29917 : (x (-9) 8).toNat + (x (-10) 1 && x (-10) 9).toNat + (x (-11) 2 && x (-11) 10).toNat + (x (-12) 3 && x (-12) 11).toNat + (x (-13) 4 && x (-13) 12).toNat + (x (-14) 5 && x (-14) 13).toNat + (x (-15) 6 && x (-15) 14).toNat + (x (-16) 7).toNat = 1 := by have q := hd8 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29918 : (x (-10) 1 && x (-10) 9).toNat = (x (-10) 9).toNat := handr _ _ (fun h => hp9 (-10) (h))
                  have e29919 : (x (-11) 2 && x (-11) 10).toNat = (x (-11) 10).toNat := handr _ _ (fun h => hp10 (-11) (h))
                  have e29920 : (x (-12) 3 && x (-12) 11).toNat = (x (-12) 11).toNat := handr _ _ (fun h => hp11 (-12) (h))
                  have e29921 : (x (-13) 4 && x (-13) 12).toNat = (x (-13) 4).toNat := handl _ _ (fun h => hp4 (-13) (h))
                  have e29922 : (x (-14) 5 && x (-14) 13).toNat = (x (-14) 5).toNat := handl _ _ (fun h => hp5 (-14) (h))
                  have e29923 : (x (-15) 6 && x (-15) 14).toNat = (x (-15) 6).toNat := handl _ _ (fun h => hp6 (-15) (h))
                  have b29924 := hb (x (-16) 7)
                  have b29925 := hb (x (-15) 6)
                  have b29926 := hb (x (-14) 5)
                  have b29927 := hb (x (-13) 4)
                  have b29928 := hb (x (-12) 11)
                  have b29929 := hb (x (-11) 10)
                  have b29930 := hb (x (-10) 9)
                  have b29931 := hb (x (-9) 8)
                  clear * - r29917 e29918 e29919 e29920 e29921 e29922 e29923 b29924 b29925 b29926 b29927 b29928 b29929 b29930 b29931 d29868 d29884 d29900 d29586 d29453
                  omega
                have d29932 : (x (-14) 14).toNat = 1 := by
                  have r29933 : (x (-1) 1).toNat + (x (-2) 2).toNat + (x (-3) 3).toNat + (x (-4) 4).toNat + (x (-5) 5).toNat + (x (-6) 6).toNat + (x (-7) 7).toNat + (x (-8) 8).toNat + (x (-9) 9).toNat + (x (-10) 10).toNat + (x (-11) 11).toNat + (x (-12) 12).toNat + (x (-13) 13).toNat + (x (-14) 14).toNat = 3 := by have q := hcount 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29934 := hb (x (-14) 14)
                  have b29935 := hb (x (-13) 13)
                  have b29936 := hb (x (-12) 12)
                  have b29937 := hb (x (-11) 11)
                  have b29938 := hb (x (-10) 10)
                  have b29939 := hb (x (-9) 9)
                  have b29940 := hb (x (-8) 8)
                  have b29941 := hb (x (-7) 7)
                  have b29942 := hb (x (-6) 6)
                  have b29943 := hb (x (-5) 5)
                  have b29944 := hb (x (-4) 4)
                  have b29945 := hb (x (-3) 3)
                  have b29946 := hb (x (-2) 2)
                  have b29947 := hb (x (-1) 1)
                  clear * - r29933 b29934 b29935 b29936 b29937 b29938 b29939 b29940 b29941 b29942 b29943 b29944 b29945 b29946 b29947 d28591 d28900 d28929 d29248 d29264 d29280 d29300 d29647 d29667 d29687 d29707 d29619 d29614
                  omega
                have d29948 : (x (-15) 1).toNat = 0 := by
                  have r29949 : (x (-14) 14).toNat + (x (-15) 1).toNat = 1 := by have q := hd14 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29950 := hb (x (-15) 1)
                  have b29951 := hb (x (-14) 14)
                  clear * - r29949 b29950 b29951 d29932
                  omega
                have d29952 : (x (-15) 1 && x (-15) 14).toNat = 0 := by
                  have r29953 := hand1 (x (-15) 1) (x (-15) 14)
                  have b29954 := hb (x (-15) 1)
                  have b29955 := hb (x (-15) 1 && x (-15) 14)
                  clear * - r29953 b29954 b29955 d29948
                  omega
                have d29956 : (x (-16) 2).toNat = 1 := by
                  have r29957 : 1 ≤ (x (-14) 13).toNat + (x (-15) 1 && x (-15) 14).toNat + (x (-16) 2).toNat := by have q := hcov13 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29958 := hb (x (-16) 2)
                  have b29959 := hb (x (-14) 13)
                  have b29960 := hb (x (-15) 1 && x (-15) 14)
                  clear * - r29957 b29958 b29959 b29960 d29449 d29952
                  omega
                have d29961 : (x (-16) 14).toNat = 1 := by
                  have r29962 : (x (-16) 2).toNat ≤ (x (-16) 14).toNat := himp _ _ (hp2 (-16))
                  have b29963 := hb (x (-16) 2)
                  have b29964 := hb (x (-16) 14)
                  clear * - r29962 b29963 b29964 d29956
                  omega
                have d29965 : (x (-17) 1).toNat = 0 := by
                  have r29966 : (x (-16) 14).toNat + (x (-17) 1).toNat = 1 := by have q := hd14 (-16); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b29967 := hb (x (-17) 1)
                  have b29968 := hb (x (-16) 14)
                  clear * - r29966 b29967 b29968 d29961
                  omega
                have d29969 : (x (-17) 13).toNat = 0 := by
                  have r29970 : (x (-17) 13).toNat ≤ (x (-17) 1).toNat := himp _ _ (hp13 (-17))
                  have b29971 := hb (x (-17) 1)
                  have b29972 := hb (x (-17) 13)
                  clear * - r29970 b29971 b29972 d29965
                  omega
                have d29973 : (x (-14) 12).toNat = 0 := by
                  have r29974 : (x (-14) 12).toNat + (x (-15) 1 && x (-15) 13).toNat + (x (-16) 2 && x (-16) 14).toNat + (x (-17) 3).toNat = 1 := by have q := hd12 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29975 : (x (-15) 1 && x (-15) 13).toNat = (x (-15) 13).toNat := handr _ _ (fun h => hp13 (-15) (h))
                  have e29976 : (x (-16) 2 && x (-16) 14).toNat = (x (-16) 2).toNat := handl _ _ (fun h => hp2 (-16) (h))
                  have b29977 := hb (x (-17) 3)
                  have b29978 := hb (x (-16) 2)
                  have b29979 := hb (x (-15) 13)
                  have b29980 := hb (x (-14) 12)
                  clear * - r29974 e29975 e29976 b29977 b29978 b29979 b29980 d29956
                  omega
                have d29981 : (x (-15) 13).toNat = 0 := by
                  have r29982 : (x (-14) 12).toNat + (x (-15) 1 && x (-15) 13).toNat + (x (-16) 2 && x (-16) 14).toNat + (x (-17) 3).toNat = 1 := by have q := hd12 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29983 : (x (-15) 1 && x (-15) 13).toNat = (x (-15) 13).toNat := handr _ _ (fun h => hp13 (-15) (h))
                  have e29984 : (x (-16) 2 && x (-16) 14).toNat = (x (-16) 2).toNat := handl _ _ (fun h => hp2 (-16) (h))
                  have b29985 := hb (x (-17) 3)
                  have b29986 := hb (x (-16) 2)
                  have b29987 := hb (x (-15) 13)
                  have b29988 := hb (x (-14) 12)
                  clear * - r29982 e29983 e29984 b29985 b29986 b29987 b29988 d29973 d29956
                  omega
                have d29989 : (x (-17) 3).toNat = 0 := by
                  have r29990 : (x (-14) 12).toNat + (x (-15) 1 && x (-15) 13).toNat + (x (-16) 2 && x (-16) 14).toNat + (x (-17) 3).toNat = 1 := by have q := hd12 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e29991 : (x (-15) 1 && x (-15) 13).toNat = (x (-15) 13).toNat := handr _ _ (fun h => hp13 (-15) (h))
                  have e29992 : (x (-16) 2 && x (-16) 14).toNat = (x (-16) 2).toNat := handl _ _ (fun h => hp2 (-16) (h))
                  have b29993 := hb (x (-17) 3)
                  have b29994 := hb (x (-16) 2)
                  have b29995 := hb (x (-15) 13)
                  have b29996 := hb (x (-14) 12)
                  clear * - r29990 e29991 e29992 b29993 b29994 b29995 b29996 d29973 d29981 d29956
                  omega
                have d29997 : (x (-17) 3 && x (-17) 14).toNat = 0 := by
                  have r29998 := hand1 (x (-17) 3) (x (-17) 14)
                  have b29999 := hb (x (-17) 3)
                  have b30000 := hb (x (-17) 3 && x (-17) 14)
                  clear * - r29998 b29999 b30000 d29989
                  omega
                have d30001 : (x (-17) 3 && x (-17) 12).toNat = 0 := by
                  have r30002 := hand1 (x (-17) 3) (x (-17) 12)
                  have b30003 := hb (x (-17) 3)
                  have b30004 := hb (x (-17) 3 && x (-17) 12)
                  clear * - r30002 b30003 b30004 d29989
                  omega
                have d30005 : (x (-17) 11).toNat = 0 := by
                  have r30006 : (x (-17) 11).toNat ≤ (x (-17) 3).toNat := himp _ _ (hp11 (-17))
                  have b30007 := hb (x (-17) 3)
                  have b30008 := hb (x (-17) 11)
                  clear * - r30006 b30007 b30008 d29989
                  omega
                have d30009 : (x (-15) 1 && x (-15) 12).toNat = 0 := by
                  have r30010 := hand1 (x (-15) 1) (x (-15) 12)
                  have b30011 := hb (x (-15) 1)
                  have b30012 := hb (x (-15) 1 && x (-15) 12)
                  clear * - r30010 b30011 b30012 d29948
                  omega
                have d30013 : (x (-15) 9).toNat = 0 := by
                  have r30014 : (x (-15) 9).toNat ≤ (x (-15) 1).toNat := himp _ _ (hp9 (-15))
                  have b30015 := hb (x (-15) 1)
                  have b30016 := hb (x (-15) 9)
                  clear * - r30014 b30015 b30016 d29948
                  omega
                have d30017 : (x (-15) 14).toNat = 1 := by
                  have r30018 : (x (-2) 1).toNat + (x (-3) 2).toNat + (x (-4) 3).toNat + (x (-5) 4).toNat + (x (-6) 5).toNat + (x (-7) 6).toNat + (x (-8) 7).toNat + (x (-9) 8).toNat + (x (-10) 9).toNat + (x (-11) 10).toNat + (x (-12) 11).toNat + (x (-13) 12).toNat + (x (-14) 13).toNat + (x (-15) 14).toNat = 3 := by have q := hcount (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30019 := hb (x (-15) 14)
                  have b30020 := hb (x (-14) 13)
                  have b30021 := hb (x (-13) 12)
                  have b30022 := hb (x (-12) 11)
                  have b30023 := hb (x (-11) 10)
                  have b30024 := hb (x (-10) 9)
                  have b30025 := hb (x (-9) 8)
                  have b30026 := hb (x (-8) 7)
                  have b30027 := hb (x (-7) 6)
                  have b30028 := hb (x (-6) 5)
                  have b30029 := hb (x (-5) 4)
                  have b30030 := hb (x (-4) 3)
                  have b30031 := hb (x (-3) 2)
                  have b30032 := hb (x (-2) 1)
                  clear * - r30018 b30019 b30020 b30021 b30022 b30023 b30024 b30025 b30026 b30027 b30028 b30029 b30030 b30031 b30032 d28974 d28986 d28998 d29179 d29199 d29219 d29320 d29868 d29884 d29900 d29916 d29590 d29449
                  omega
                have d30033 : (x (-16) 1).toNat = 0 := by
                  have r30034 : (x (-15) 14).toNat + (x (-16) 1).toNat = 1 := by have q := hd14 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30035 := hb (x (-16) 1)
                  have b30036 := hb (x (-15) 14)
                  clear * - r30034 b30035 b30036 d30017
                  omega
                have d30037 : (x (-16) 1 && x (-16) 14).toNat = 0 := by
                  have r30038 := hand1 (x (-16) 1) (x (-16) 14)
                  have b30039 := hb (x (-16) 1)
                  have b30040 := hb (x (-16) 1 && x (-16) 14)
                  clear * - r30038 b30039 b30040 d30033
                  omega
                have d30041 : (x (-17) 2).toNat = 1 := by
                  have r30042 : 1 ≤ (x (-15) 13).toNat + (x (-16) 1 && x (-16) 14).toNat + (x (-17) 2).toNat := by have q := hcov13 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30043 := hb (x (-17) 2)
                  have b30044 := hb (x (-15) 13)
                  have b30045 := hb (x (-16) 1 && x (-16) 14)
                  clear * - r30042 b30043 b30044 b30045 d29981 d30037
                  omega
                have d30046 : (x (-17) 14).toNat = 1 := by
                  have r30047 : (x (-17) 2).toNat ≤ (x (-17) 14).toNat := himp _ _ (hp2 (-17))
                  have b30048 := hb (x (-17) 2)
                  have b30049 := hb (x (-17) 14)
                  clear * - r30047 b30048 b30049 d30041
                  omega
                have d30050 : (x (-18) 1).toNat = 0 := by
                  have r30051 : (x (-17) 14).toNat + (x (-18) 1).toNat = 1 := by have q := hd14 (-17); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30052 := hb (x (-18) 1)
                  have b30053 := hb (x (-17) 14)
                  clear * - r30051 b30052 b30053 d30046
                  omega
                have d30054 : (x (-18) 1 && x (-18) 14).toNat = 0 := by
                  have r30055 := hand1 (x (-18) 1) (x (-18) 14)
                  have b30056 := hb (x (-18) 1)
                  have b30057 := hb (x (-18) 1 && x (-18) 14)
                  clear * - r30055 b30056 b30057 d30050
                  omega
                have d30058 : (x (-19) 2).toNat = 1 := by
                  have r30059 : 1 ≤ (x (-17) 13).toNat + (x (-18) 1 && x (-18) 14).toNat + (x (-19) 2).toNat := by have q := hcov13 (-17); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30060 := hb (x (-19) 2)
                  have b30061 := hb (x (-17) 13)
                  have b30062 := hb (x (-18) 1 && x (-18) 14)
                  clear * - r30059 b30060 b30061 b30062 d29969 d30054
                  omega
                have d30063 : (x (-17) 12).toNat = 0 := by
                  have r30064 : (x (-17) 12).toNat + (x (-18) 1 && x (-18) 13).toNat + (x (-19) 2 && x (-19) 14).toNat + (x (-20) 3).toNat = 1 := by have q := hd12 (-17); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30065 : (x (-18) 1 && x (-18) 13).toNat = (x (-18) 13).toNat := handr _ _ (fun h => hp13 (-18) (h))
                  have e30066 : (x (-19) 2 && x (-19) 14).toNat = (x (-19) 2).toNat := handl _ _ (fun h => hp2 (-19) (h))
                  have b30067 := hb (x (-20) 3)
                  have b30068 := hb (x (-19) 2)
                  have b30069 := hb (x (-18) 13)
                  have b30070 := hb (x (-17) 12)
                  clear * - r30064 e30065 e30066 b30067 b30068 b30069 b30070 d30058
                  omega
                have d30071 : (x (-18) 13).toNat = 0 := by
                  have r30072 : (x (-17) 12).toNat + (x (-18) 1 && x (-18) 13).toNat + (x (-19) 2 && x (-19) 14).toNat + (x (-20) 3).toNat = 1 := by have q := hd12 (-17); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30073 : (x (-18) 1 && x (-18) 13).toNat = (x (-18) 13).toNat := handr _ _ (fun h => hp13 (-18) (h))
                  have e30074 : (x (-19) 2 && x (-19) 14).toNat = (x (-19) 2).toNat := handl _ _ (fun h => hp2 (-19) (h))
                  have b30075 := hb (x (-20) 3)
                  have b30076 := hb (x (-19) 2)
                  have b30077 := hb (x (-18) 13)
                  have b30078 := hb (x (-17) 12)
                  clear * - r30072 e30073 e30074 b30075 b30076 b30077 b30078 d30063 d30058
                  omega
                have d30079 : (x (-18) 4 && x (-18) 13).toNat = 0 := by
                  have r30080 := hand2 (x (-18) 4) (x (-18) 13)
                  have b30081 := hb (x (-18) 13)
                  have b30082 := hb (x (-18) 4 && x (-18) 13)
                  clear * - r30080 b30081 b30082 d30071
                  omega
                have d30083 : (x (-15) 12).toNat = 0 := by
                  have r30084 : (x (-15) 12).toNat + (x (-16) 1 && x (-16) 13).toNat + (x (-17) 2 && x (-17) 14).toNat + (x (-18) 3).toNat = 1 := by have q := hd12 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30085 : (x (-16) 1 && x (-16) 13).toNat = (x (-16) 13).toNat := handr _ _ (fun h => hp13 (-16) (h))
                  have e30086 : (x (-17) 2 && x (-17) 14).toNat = (x (-17) 2).toNat := handl _ _ (fun h => hp2 (-17) (h))
                  have b30087 := hb (x (-18) 3)
                  have b30088 := hb (x (-17) 2)
                  have b30089 := hb (x (-16) 13)
                  have b30090 := hb (x (-15) 12)
                  clear * - r30084 e30085 e30086 b30087 b30088 b30089 b30090 d30041
                  omega
                have d30091 : (x (-16) 13).toNat = 0 := by
                  have r30092 : (x (-15) 12).toNat + (x (-16) 1 && x (-16) 13).toNat + (x (-17) 2 && x (-17) 14).toNat + (x (-18) 3).toNat = 1 := by have q := hd12 (-15); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30093 : (x (-16) 1 && x (-16) 13).toNat = (x (-16) 13).toNat := handr _ _ (fun h => hp13 (-16) (h))
                  have e30094 : (x (-17) 2 && x (-17) 14).toNat = (x (-17) 2).toNat := handl _ _ (fun h => hp2 (-17) (h))
                  have b30095 := hb (x (-18) 3)
                  have b30096 := hb (x (-17) 2)
                  have b30097 := hb (x (-16) 13)
                  have b30098 := hb (x (-15) 12)
                  clear * - r30092 e30093 e30094 b30095 b30096 b30097 b30098 d30083 d30041
                  omega
                have d30099 : (x (-16) 2 && x (-16) 13).toNat = 0 := by
                  have r30100 := hand2 (x (-16) 2) (x (-16) 13)
                  have b30101 := hb (x (-16) 13)
                  have b30102 := hb (x (-16) 2 && x (-16) 13)
                  clear * - r30100 b30101 b30102 d30091
                  omega
                have d30103 : (x (-18) 4).toNat = 1 := by
                  have r30104 : 1 ≤ (x (-14) 11).toNat + (x (-15) 1 && x (-15) 12).toNat + (x (-16) 2 && x (-16) 13).toNat + (x (-17) 3 && x (-17) 14).toNat + (x (-18) 4).toNat := by have q := hcov11 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30105 := hb (x (-18) 4)
                  have b30106 := hb (x (-14) 11)
                  have b30107 := hb (x (-15) 1 && x (-15) 12)
                  have b30108 := hb (x (-16) 2 && x (-16) 13)
                  have b30109 := hb (x (-17) 3 && x (-17) 14)
                  clear * - r30104 b30105 b30106 b30107 b30108 b30109 d29852 d30009 d30099 d29997
                  omega
                have d30110 : (x (-14) 8).toNat = 0 := by
                  have r30111 : (x (-14) 8).toNat + (x (-15) 1 && x (-15) 9).toNat + (x (-16) 2 && x (-16) 10).toNat + (x (-17) 3 && x (-17) 11).toNat + (x (-18) 4 && x (-18) 12).toNat + (x (-19) 5 && x (-19) 13).toNat + (x (-20) 6 && x (-20) 14).toNat + (x (-21) 7).toNat = 1 := by have q := hd8 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30112 : (x (-15) 1 && x (-15) 9).toNat = (x (-15) 9).toNat := handr _ _ (fun h => hp9 (-15) (h))
                  have e30113 : (x (-16) 2 && x (-16) 10).toNat = (x (-16) 10).toNat := handr _ _ (fun h => hp10 (-16) (h))
                  have e30114 : (x (-17) 3 && x (-17) 11).toNat = (x (-17) 11).toNat := handr _ _ (fun h => hp11 (-17) (h))
                  have e30115 : (x (-18) 4 && x (-18) 12).toNat = (x (-18) 4).toNat := handl _ _ (fun h => hp4 (-18) (h))
                  have e30116 : (x (-19) 5 && x (-19) 13).toNat = (x (-19) 5).toNat := handl _ _ (fun h => hp5 (-19) (h))
                  have e30117 : (x (-20) 6 && x (-20) 14).toNat = (x (-20) 6).toNat := handl _ _ (fun h => hp6 (-20) (h))
                  have b30118 := hb (x (-21) 7)
                  have b30119 := hb (x (-20) 6)
                  have b30120 := hb (x (-19) 5)
                  have b30121 := hb (x (-18) 4)
                  have b30122 := hb (x (-17) 11)
                  have b30123 := hb (x (-16) 10)
                  have b30124 := hb (x (-15) 9)
                  have b30125 := hb (x (-14) 8)
                  clear * - r30111 e30112 e30113 e30114 e30115 e30116 e30117 b30118 b30119 b30120 b30121 b30122 b30123 b30124 b30125 d30013 d30005 d30103
                  omega
                have d30126 : (x (-16) 10).toNat = 0 := by
                  have r30127 : (x (-14) 8).toNat + (x (-15) 1 && x (-15) 9).toNat + (x (-16) 2 && x (-16) 10).toNat + (x (-17) 3 && x (-17) 11).toNat + (x (-18) 4 && x (-18) 12).toNat + (x (-19) 5 && x (-19) 13).toNat + (x (-20) 6 && x (-20) 14).toNat + (x (-21) 7).toNat = 1 := by have q := hd8 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30128 : (x (-15) 1 && x (-15) 9).toNat = (x (-15) 9).toNat := handr _ _ (fun h => hp9 (-15) (h))
                  have e30129 : (x (-16) 2 && x (-16) 10).toNat = (x (-16) 10).toNat := handr _ _ (fun h => hp10 (-16) (h))
                  have e30130 : (x (-17) 3 && x (-17) 11).toNat = (x (-17) 11).toNat := handr _ _ (fun h => hp11 (-17) (h))
                  have e30131 : (x (-18) 4 && x (-18) 12).toNat = (x (-18) 4).toNat := handl _ _ (fun h => hp4 (-18) (h))
                  have e30132 : (x (-19) 5 && x (-19) 13).toNat = (x (-19) 5).toNat := handl _ _ (fun h => hp5 (-19) (h))
                  have e30133 : (x (-20) 6 && x (-20) 14).toNat = (x (-20) 6).toNat := handl _ _ (fun h => hp6 (-20) (h))
                  have b30134 := hb (x (-21) 7)
                  have b30135 := hb (x (-20) 6)
                  have b30136 := hb (x (-19) 5)
                  have b30137 := hb (x (-18) 4)
                  have b30138 := hb (x (-17) 11)
                  have b30139 := hb (x (-16) 10)
                  have b30140 := hb (x (-15) 9)
                  have b30141 := hb (x (-14) 8)
                  clear * - r30127 e30128 e30129 e30130 e30131 e30132 e30133 b30134 b30135 b30136 b30137 b30138 b30139 b30140 b30141 d30110 d30013 d30005 d30103
                  omega
                have d30142 : (x (-19) 5).toNat = 0 := by
                  have r30143 : (x (-14) 8).toNat + (x (-15) 1 && x (-15) 9).toNat + (x (-16) 2 && x (-16) 10).toNat + (x (-17) 3 && x (-17) 11).toNat + (x (-18) 4 && x (-18) 12).toNat + (x (-19) 5 && x (-19) 13).toNat + (x (-20) 6 && x (-20) 14).toNat + (x (-21) 7).toNat = 1 := by have q := hd8 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30144 : (x (-15) 1 && x (-15) 9).toNat = (x (-15) 9).toNat := handr _ _ (fun h => hp9 (-15) (h))
                  have e30145 : (x (-16) 2 && x (-16) 10).toNat = (x (-16) 10).toNat := handr _ _ (fun h => hp10 (-16) (h))
                  have e30146 : (x (-17) 3 && x (-17) 11).toNat = (x (-17) 11).toNat := handr _ _ (fun h => hp11 (-17) (h))
                  have e30147 : (x (-18) 4 && x (-18) 12).toNat = (x (-18) 4).toNat := handl _ _ (fun h => hp4 (-18) (h))
                  have e30148 : (x (-19) 5 && x (-19) 13).toNat = (x (-19) 5).toNat := handl _ _ (fun h => hp5 (-19) (h))
                  have e30149 : (x (-20) 6 && x (-20) 14).toNat = (x (-20) 6).toNat := handl _ _ (fun h => hp6 (-20) (h))
                  have b30150 := hb (x (-21) 7)
                  have b30151 := hb (x (-20) 6)
                  have b30152 := hb (x (-19) 5)
                  have b30153 := hb (x (-18) 4)
                  have b30154 := hb (x (-17) 11)
                  have b30155 := hb (x (-16) 10)
                  have b30156 := hb (x (-15) 9)
                  have b30157 := hb (x (-14) 8)
                  clear * - r30143 e30144 e30145 e30146 e30147 e30148 e30149 b30150 b30151 b30152 b30153 b30154 b30155 b30156 b30157 d30110 d30013 d30126 d30005 d30103
                  omega
                have d30158 : (x (-19) 5 && x (-19) 14).toNat = 0 := by
                  have r30159 := hand1 (x (-19) 5) (x (-19) 14)
                  have b30160 := hb (x (-19) 5)
                  have b30161 := hb (x (-19) 5 && x (-19) 14)
                  clear * - r30159 b30160 b30161 d30142
                  omega
                have d30162 : (x (-20) 6).toNat = 1 := by
                  have r30163 : 1 ≤ (x (-14) 9).toNat + (x (-15) 1 && x (-15) 10).toNat + (x (-16) 2 && x (-16) 11).toNat + (x (-17) 3 && x (-17) 12).toNat + (x (-18) 4 && x (-18) 13).toNat + (x (-19) 5 && x (-19) 14).toNat + (x (-20) 6).toNat := by have q := hcov9 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30164 := hb (x (-20) 6)
                  have b30165 := hb (x (-14) 9)
                  have b30166 := hb (x (-15) 1 && x (-15) 10)
                  have b30167 := hb (x (-16) 2 && x (-16) 11)
                  have b30168 := hb (x (-17) 3 && x (-17) 12)
                  have b30169 := hb (x (-18) 4 && x (-18) 13)
                  have b30170 := hb (x (-19) 5 && x (-19) 14)
                  clear * - r30163 b30164 b30165 b30166 b30167 b30168 b30169 b30170 d29457 d29610 d29760 d30001 d30079 d30158
                  omega
                have r30171 : (x (-14) 8).toNat + (x (-15) 1 && x (-15) 9).toNat + (x (-16) 2 && x (-16) 10).toNat + (x (-17) 3 && x (-17) 11).toNat + (x (-18) 4 && x (-18) 12).toNat + (x (-19) 5 && x (-19) 13).toNat + (x (-20) 6 && x (-20) 14).toNat + (x (-21) 7).toNat = 1 := by have q := hd8 (-14); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e30172 : (x (-15) 1 && x (-15) 9).toNat = (x (-15) 9).toNat := handr _ _ (fun h => hp9 (-15) (h))
                have e30173 : (x (-16) 2 && x (-16) 10).toNat = (x (-16) 10).toNat := handr _ _ (fun h => hp10 (-16) (h))
                have e30174 : (x (-17) 3 && x (-17) 11).toNat = (x (-17) 11).toNat := handr _ _ (fun h => hp11 (-17) (h))
                have e30175 : (x (-18) 4 && x (-18) 12).toNat = (x (-18) 4).toNat := handl _ _ (fun h => hp4 (-18) (h))
                have e30176 : (x (-19) 5 && x (-19) 13).toNat = (x (-19) 5).toNat := handl _ _ (fun h => hp5 (-19) (h))
                have e30177 : (x (-20) 6 && x (-20) 14).toNat = (x (-20) 6).toNat := handl _ _ (fun h => hp6 (-20) (h))
                have b30178 := hb (x (-21) 7)
                have b30179 := hb (x (-20) 6)
                have b30180 := hb (x (-19) 5)
                have b30181 := hb (x (-18) 4)
                have b30182 := hb (x (-17) 11)
                have b30183 := hb (x (-16) 10)
                have b30184 := hb (x (-15) 9)
                have b30185 := hb (x (-14) 8)
                linarith only [r30171, e30172, e30173, e30174, e30175, e30176, e30177, b30178, b30179, b30180, b30181, b30182, b30183, b30184, b30185, d30110, d30013, d30126, d30005, d30103, d30142, d30162]
              · have f30186 : (x 0 13).toNat = 1 := by rw [h28898]; rfl
                have d30187 : (x 1 12).toNat = 0 := by
                  have r30188 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30189 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                  have e30190 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                  have b30191 := hb (x (-2) 3)
                  have b30192 := hb (x (-1) 2)
                  have b30193 := hb (x 0 13)
                  have b30194 := hb (x 1 12)
                  clear * - r30188 e30189 e30190 b30191 b30192 b30193 b30194 f30186
                  omega
                have d30195 : (x 1 4).toNat = 0 := by
                  have r30196 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
                  have b30197 := hb (x 1 4)
                  have b30198 := hb (x 1 12)
                  clear * - r30196 b30197 b30198 d30187
                  omega
                have d30199 : (x (-1) 2).toNat = 0 := by
                  have r30200 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30201 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                  have e30202 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                  have b30203 := hb (x (-2) 3)
                  have b30204 := hb (x (-1) 2)
                  have b30205 := hb (x 0 13)
                  have b30206 := hb (x 1 12)
                  clear * - r30200 e30201 e30202 b30203 b30204 b30205 b30206 d30187 f30186
                  omega
                have d30207 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
                  have r30208 := hand1 (x (-1) 2) (x (-1) 12)
                  have b30209 := hb (x (-1) 2)
                  have b30210 := hb (x (-1) 2 && x (-1) 12)
                  clear * - r30208 b30209 b30210 d30199
                  omega
                have d30211 : (x (-2) 3).toNat = 0 := by
                  have r30212 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30213 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
                  have e30214 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
                  have b30215 := hb (x (-2) 3)
                  have b30216 := hb (x (-1) 2)
                  have b30217 := hb (x 0 13)
                  have b30218 := hb (x 1 12)
                  clear * - r30212 e30213 e30214 b30215 b30216 b30217 b30218 d30187 f30186 d30199
                  omega
                have d30219 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
                  have r30220 := hand1 (x (-2) 3) (x (-2) 14)
                  have b30221 := hb (x (-2) 3)
                  have b30222 := hb (x (-2) 3 && x (-2) 14)
                  clear * - r30220 b30221 b30222 d30211
                  omega
                have d30223 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
                  have r30224 := hand1 (x (-2) 3) (x (-2) 13)
                  have b30225 := hb (x (-2) 3)
                  have b30226 := hb (x (-2) 3 && x (-2) 13)
                  clear * - r30224 b30225 b30226 d30211
                  omega
                have d30227 : (x (-3) 4).toNat = 1 := by
                  have r30228 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30229 := hb (x (-3) 4)
                  have b30230 := hb (x 1 11)
                  have b30231 := hb (x 0 1 && x 0 12)
                  have b30232 := hb (x (-1) 2 && x (-1) 13)
                  have b30233 := hb (x (-2) 3 && x (-2) 14)
                  clear * - r30228 b30229 b30230 b30231 b30232 b30233 g6 d28202 d28603 d30219
                  omega
                have d30234 : (x (-3) 12).toNat = 1 := by
                  have r30235 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
                  have b30236 := hb (x (-3) 4)
                  have b30237 := hb (x (-3) 12)
                  clear * - r30235 b30236 b30237 d30227
                  omega
                have d30238 : (x (-4) 13).toNat = 0 := by
                  have r30239 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30240 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                  have e30241 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                  have b30242 := hb (x (-6) 3)
                  have b30243 := hb (x (-5) 2)
                  have b30244 := hb (x (-4) 13)
                  have b30245 := hb (x (-3) 12)
                  clear * - r30239 e30240 e30241 b30242 b30243 b30244 b30245 d30234
                  omega
                have d30246 : (x (-4) 5).toNat = 0 := by
                  have r30247 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
                  have b30248 := hb (x (-4) 5)
                  have b30249 := hb (x (-4) 13)
                  clear * - r30247 b30248 b30249 d30238
                  omega
                have d30250 : (x (-5) 2).toNat = 0 := by
                  have r30251 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30252 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
                  have e30253 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
                  have b30254 := hb (x (-6) 3)
                  have b30255 := hb (x (-5) 2)
                  have b30256 := hb (x (-4) 13)
                  have b30257 := hb (x (-3) 12)
                  clear * - r30251 e30252 e30253 b30254 b30255 b30256 b30257 d30234 d30238
                  omega
                have d30258 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
                  have r30259 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30260 := hb (x (-4) 5)
                  have b30261 := hb (x 1 10)
                  have b30262 := hb (x 0 1 && x 0 11)
                  have b30263 := hb (x (-1) 2 && x (-1) 12)
                  have b30264 := hb (x (-2) 3 && x (-2) 13)
                  have b30265 := hb (x (-3) 4 && x (-3) 14)
                  clear * - r30259 b30260 b30261 b30262 b30263 b30264 b30265 g5 d28870 d30207 d30223 d30246
                  omega
                have d30266 : (x (-3) 14).toNat = 1 := by
                  have r30267 := hand2 (x (-3) 4) (x (-3) 14)
                  have b30268 := hb (x (-3) 14)
                  have b30269 := hb (x (-3) 4 && x (-3) 14)
                  clear * - r30267 b30268 b30269 d30258
                  omega
                have d30270 : (x (-4) 1).toNat = 0 := by
                  have r30271 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30272 := hb (x (-4) 1)
                  have b30273 := hb (x (-3) 14)
                  clear * - r30271 b30272 b30273 d30266
                  omega
                have d30274 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
                  have r30275 := hand1 (x (-4) 1) (x (-4) 14)
                  have b30276 := hb (x (-4) 1)
                  have b30277 := hb (x (-4) 1 && x (-4) 14)
                  clear * - r30275 b30276 b30277 d30270
                  omega
                have d30278 : (x (-3) 13).toNat = 1 := by
                  have r30279 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30280 := hb (x (-5) 2)
                  have b30281 := hb (x (-3) 13)
                  have b30282 := hb (x (-4) 1 && x (-4) 14)
                  clear * - r30279 b30280 b30281 b30282 d30274 d30250
                  omega
                have d30283 : (x (-3) 1).toNat = 1 := by
                  have r30284 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
                  have b30285 := hb (x (-3) 1)
                  have b30286 := hb (x (-3) 13)
                  clear * - r30284 b30285 b30286 d30278
                  omega
                have d30287 : (x (-2) 14).toNat = 0 := by
                  have r30288 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30289 := hb (x (-3) 1)
                  have b30290 := hb (x (-2) 14)
                  clear * - r30288 b30289 b30290 d30283
                  omega
                have d30291 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
                  have r30292 := hand2 (x (-2) 1) (x (-2) 14)
                  have b30293 := hb (x (-2) 14)
                  have b30294 := hb (x (-2) 1 && x (-2) 14)
                  clear * - r30292 b30293 b30294 d30287
                  omega
                have d30295 : (x (-3) 2).toNat = 1 := by
                  have r30296 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30297 := hb (x (-3) 2)
                  have b30298 := hb (x (-1) 13)
                  have b30299 := hb (x (-2) 1 && x (-2) 14)
                  clear * - r30296 b30297 b30298 b30299 d28599 d30291
                  omega
                have d30300 : (x (-1) 12).toNat = 0 := by
                  have r30301 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30302 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e30303 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b30304 := hb (x (-4) 3)
                  have b30305 := hb (x (-3) 2)
                  have b30306 := hb (x (-2) 13)
                  have b30307 := hb (x (-1) 12)
                  clear * - r30301 e30302 e30303 b30304 b30305 b30306 b30307 d30295
                  omega
                have d30308 : (x (-1) 4).toNat = 0 := by
                  have r30309 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
                  have b30310 := hb (x (-1) 4)
                  have b30311 := hb (x (-1) 12)
                  clear * - r30309 b30310 b30311 d30300
                  omega
                have d30312 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
                  have r30313 := hand1 (x (-1) 4) (x (-1) 14)
                  have b30314 := hb (x (-1) 4)
                  have b30315 := hb (x (-1) 4 && x (-1) 14)
                  clear * - r30313 b30314 b30315 d30308
                  omega
                have d30316 : (x (-2) 13).toNat = 0 := by
                  have r30317 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30318 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
                  have e30319 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
                  have b30320 := hb (x (-4) 3)
                  have b30321 := hb (x (-3) 2)
                  have b30322 := hb (x (-2) 13)
                  have b30323 := hb (x (-1) 12)
                  clear * - r30317 e30318 e30319 b30320 b30321 b30322 b30323 d30300 d30295
                  omega
                have d30324 : (x (-2) 5).toNat = 0 := by
                  have r30325 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
                  have b30326 := hb (x (-2) 5)
                  have b30327 := hb (x (-2) 13)
                  clear * - r30325 b30326 b30327 d30316
                  omega
                have d30328 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
                  have r30329 := hand1 (x (-2) 5) (x (-2) 14)
                  have b30330 := hb (x (-2) 5)
                  have b30331 := hb (x (-2) 5 && x (-2) 14)
                  clear * - r30329 b30330 b30331 d30324
                  omega
                have d30332 : (x 3 10).toNat = 1 := by
                  have r30333 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30334 := hb (x (-2) 5)
                  have b30335 := hb (x 3 10)
                  have b30336 := hb (x 2 1 && x 2 11)
                  have b30337 := hb (x 1 2 && x 1 12)
                  have b30338 := hb (x 0 3 && x 0 13)
                  have b30339 := hb (x (-1) 4 && x (-1) 14)
                  clear * - r30333 b30334 b30335 b30336 b30337 b30338 b30339 d28756 g23 d28862 d30312 d30324
                  omega
                have d30340 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
                  have r30341 := hand2 (x (-2) 4) (x (-2) 14)
                  have b30342 := hb (x (-2) 14)
                  have b30343 := hb (x (-2) 4 && x (-2) 14)
                  clear * - r30341 b30342 b30343 d30287
                  omega
                have d30344 : (x (-3) 5).toNat = 1 := by
                  have r30345 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30346 := hb (x (-3) 5)
                  have b30347 := hb (x 2 10)
                  have b30348 := hb (x 1 1 && x 1 11)
                  have b30349 := hb (x 0 2 && x 0 12)
                  have b30350 := hb (x (-1) 3 && x (-1) 13)
                  have b30351 := hb (x (-2) 4 && x (-2) 14)
                  clear * - r30345 b30346 b30347 b30348 b30349 b30350 b30351 g9 g22 d28206 d28607 d30340
                  omega
                have d30352 : (x (-2) 6).toNat = 0 := by
                  have r30353 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
                  have b30354 := hb (x (-2) 6)
                  have b30355 := hb (x (-2) 14)
                  clear * - r30353 b30354 b30355 d30287
                  omega
                have d30356 : (x (-2) 4 && x (-2) 6).toNat = 0 := by
                  have r30357 := hand2 (x (-2) 4) (x (-2) 6)
                  have b30358 := hb (x (-2) 6)
                  have b30359 := hb (x (-2) 4 && x (-2) 6)
                  clear * - r30357 b30358 b30359 d30352
                  omega
                have d30360 : (x (-2) 12).toNat = 0 := by
                  have r30361 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30362 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
                  have e30363 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
                  have b30364 := hb (x (-5) 3)
                  have b30365 := hb (x (-4) 2)
                  have b30366 := hb (x (-3) 13)
                  have b30367 := hb (x (-2) 12)
                  clear * - r30361 e30362 e30363 b30364 b30365 b30366 b30367 d30278
                  omega
                have d30368 : (x (-2) 4).toNat = 0 := by
                  have r30369 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
                  have b30370 := hb (x (-2) 4)
                  have b30371 := hb (x (-2) 12)
                  clear * - r30369 b30370 b30371 d30360
                  omega
                have d30372 : (x 5 8).toNat = 0 := by
                  have r30373 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30374 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                  have e30375 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                  have e30376 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                  have e30377 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                  have e30378 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                  have e30379 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                  have b30380 := hb (x (-2) 7)
                  have b30381 := hb (x (-1) 6)
                  have b30382 := hb (x 0 5)
                  have b30383 := hb (x 1 4)
                  have b30384 := hb (x 2 11)
                  have b30385 := hb (x 3 10)
                  have b30386 := hb (x 4 9)
                  have b30387 := hb (x 5 8)
                  clear * - r30373 e30374 e30375 e30376 e30377 e30378 e30379 b30380 b30381 b30382 b30383 b30384 b30385 b30386 b30387 d30332 d28796 d30195 f28887
                  omega
                have d30388 : (x 4 9).toNat = 0 := by
                  have r30389 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30390 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
                  have e30391 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
                  have e30392 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
                  have e30393 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
                  have e30394 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
                  have e30395 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
                  have b30396 := hb (x (-2) 7)
                  have b30397 := hb (x (-1) 6)
                  have b30398 := hb (x 0 5)
                  have b30399 := hb (x 1 4)
                  have b30400 := hb (x 2 11)
                  have b30401 := hb (x 3 10)
                  have b30402 := hb (x 4 9)
                  have b30403 := hb (x 5 8)
                  clear * - r30389 e30390 e30391 e30392 e30393 e30394 e30395 b30396 b30397 b30398 b30399 b30400 b30401 b30402 b30403 d30372 d30332 d28796 d30195 f28887
                  omega
                have d30404 : (x 2 8).toNat = 0 := by
                  have r30405 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30406 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e30407 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e30408 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e30409 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e30410 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e30411 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b30412 := hb (x (-5) 7)
                  have b30413 := hb (x (-4) 6)
                  have b30414 := hb (x (-3) 5)
                  have b30415 := hb (x (-2) 4)
                  have b30416 := hb (x (-1) 11)
                  have b30417 := hb (x 0 10)
                  have b30418 := hb (x 1 9)
                  have b30419 := hb (x 2 8)
                  clear * - r30405 e30406 e30407 e30408 e30409 e30410 e30411 b30412 b30413 b30414 b30415 b30416 b30417 b30418 b30419 f28897 d28679 d30368 d30344
                  omega
                have d30420 : (x 1 9).toNat = 0 := by
                  have r30421 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30422 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e30423 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e30424 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e30425 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e30426 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e30427 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b30428 := hb (x (-5) 7)
                  have b30429 := hb (x (-4) 6)
                  have b30430 := hb (x (-3) 5)
                  have b30431 := hb (x (-2) 4)
                  have b30432 := hb (x (-1) 11)
                  have b30433 := hb (x 0 10)
                  have b30434 := hb (x 1 9)
                  have b30435 := hb (x 2 8)
                  clear * - r30421 e30422 e30423 e30424 e30425 e30426 e30427 b30428 b30429 b30430 b30431 b30432 b30433 b30434 b30435 d30404 f28897 d28679 d30368 d30344
                  omega
                have d30436 : (x (-4) 6).toNat = 0 := by
                  have r30437 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30438 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e30439 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e30440 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e30441 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e30442 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e30443 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b30444 := hb (x (-5) 7)
                  have b30445 := hb (x (-4) 6)
                  have b30446 := hb (x (-3) 5)
                  have b30447 := hb (x (-2) 4)
                  have b30448 := hb (x (-1) 11)
                  have b30449 := hb (x 0 10)
                  have b30450 := hb (x 1 9)
                  have b30451 := hb (x 2 8)
                  clear * - r30437 e30438 e30439 e30440 e30441 e30442 e30443 b30444 b30445 b30446 b30447 b30448 b30449 b30450 b30451 d30404 d30420 f28897 d28679 d30368 d30344
                  omega
                have d30452 : (x (-4) 6 && x (-4) 8).toNat = 0 := by
                  have r30453 := hand1 (x (-4) 6) (x (-4) 8)
                  have b30454 := hb (x (-4) 6)
                  have b30455 := hb (x (-4) 6 && x (-4) 8)
                  clear * - r30453 b30454 b30455 d30436
                  omega
                have d30456 : (x (-5) 7).toNat = 0 := by
                  have r30457 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30458 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                  have e30459 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                  have e30460 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                  have e30461 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                  have e30462 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                  have e30463 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                  have b30464 := hb (x (-5) 7)
                  have b30465 := hb (x (-4) 6)
                  have b30466 := hb (x (-3) 5)
                  have b30467 := hb (x (-2) 4)
                  have b30468 := hb (x (-1) 11)
                  have b30469 := hb (x 0 10)
                  have b30470 := hb (x 1 9)
                  have b30471 := hb (x 2 8)
                  clear * - r30457 e30458 e30459 e30460 e30461 e30462 e30463 b30464 b30465 b30466 b30467 b30468 b30469 b30470 b30471 d30404 d30420 f28897 d28679 d30368 d30344 d30436
                  omega
                have d30472 : (x (-5) 7 && x (-5) 9).toNat = 0 := by
                  have r30473 := hand1 (x (-5) 7) (x (-5) 9)
                  have b30474 := hb (x (-5) 7)
                  have b30475 := hb (x (-5) 7 && x (-5) 9)
                  clear * - r30473 b30474 b30475 d30456
                  omega
                have d30476 : (x (-6) 8).toNat = 0 := by
                  have r30477 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30478 := hb (x (-12) 14)
                  have b30479 := hb (x (-11) 13)
                  have b30480 := hb (x (-10) 12)
                  have b30481 := hb (x (-9) 11)
                  have b30482 := hb (x (-8) 10)
                  have b30483 := hb (x (-7) 9)
                  have b30484 := hb (x (-6) 8)
                  have b30485 := hb (x (-5) 7)
                  have b30486 := hb (x (-4) 6)
                  have b30487 := hb (x (-3) 5)
                  have b30488 := hb (x (-2) 4)
                  have b30489 := hb (x (-1) 3)
                  have b30490 := hb (x 0 2)
                  have b30491 := hb (x 1 1)
                  clear * - r30477 b30478 b30479 b30480 b30481 b30482 b30483 b30484 b30485 b30486 b30487 b30488 b30489 b30490 b30491 g2 f28586 d28663 d30368 d30344 d30436 d30456
                  omega
                have d30492 : (x (-6) 8 && x (-6) 10).toNat = 0 := by
                  have r30493 := hand1 (x (-6) 8) (x (-6) 10)
                  have b30494 := hb (x (-6) 8)
                  have b30495 := hb (x (-6) 8 && x (-6) 10)
                  clear * - r30493 b30494 b30495 d30476
                  omega
                have d30496 : (x (-7) 9).toNat = 0 := by
                  have r30497 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30498 := hb (x (-12) 14)
                  have b30499 := hb (x (-11) 13)
                  have b30500 := hb (x (-10) 12)
                  have b30501 := hb (x (-9) 11)
                  have b30502 := hb (x (-8) 10)
                  have b30503 := hb (x (-7) 9)
                  have b30504 := hb (x (-6) 8)
                  have b30505 := hb (x (-5) 7)
                  have b30506 := hb (x (-4) 6)
                  have b30507 := hb (x (-3) 5)
                  have b30508 := hb (x (-2) 4)
                  have b30509 := hb (x (-1) 3)
                  have b30510 := hb (x 0 2)
                  have b30511 := hb (x 1 1)
                  clear * - r30497 b30498 b30499 b30500 b30501 b30502 b30503 b30504 b30505 b30506 b30507 b30508 b30509 b30510 b30511 g2 f28586 d28663 d30368 d30344 d30436 d30456 d30476
                  omega
                have d30512 : (x (-7) 9 && x (-7) 11).toNat = 0 := by
                  have r30513 := hand1 (x (-7) 9) (x (-7) 11)
                  have b30514 := hb (x (-7) 9)
                  have b30515 := hb (x (-7) 9 && x (-7) 11)
                  clear * - r30513 b30514 b30515 d30496
                  omega
                have d30516 : (x (-8) 10).toNat = 0 := by
                  have r30517 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30518 := hb (x (-12) 14)
                  have b30519 := hb (x (-11) 13)
                  have b30520 := hb (x (-10) 12)
                  have b30521 := hb (x (-9) 11)
                  have b30522 := hb (x (-8) 10)
                  have b30523 := hb (x (-7) 9)
                  have b30524 := hb (x (-6) 8)
                  have b30525 := hb (x (-5) 7)
                  have b30526 := hb (x (-4) 6)
                  have b30527 := hb (x (-3) 5)
                  have b30528 := hb (x (-2) 4)
                  have b30529 := hb (x (-1) 3)
                  have b30530 := hb (x 0 2)
                  have b30531 := hb (x 1 1)
                  clear * - r30517 b30518 b30519 b30520 b30521 b30522 b30523 b30524 b30525 b30526 b30527 b30528 b30529 b30530 b30531 g2 f28586 d28663 d30368 d30344 d30436 d30456 d30476 d30496
                  omega
                have d30532 : (x (-8) 10 && x (-8) 12).toNat = 0 := by
                  have r30533 := hand1 (x (-8) 10) (x (-8) 12)
                  have b30534 := hb (x (-8) 10)
                  have b30535 := hb (x (-8) 10 && x (-8) 12)
                  clear * - r30533 b30534 b30535 d30516
                  omega
                have d30536 : (x (-9) 11).toNat = 0 := by
                  have r30537 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30538 := hb (x (-12) 14)
                  have b30539 := hb (x (-11) 13)
                  have b30540 := hb (x (-10) 12)
                  have b30541 := hb (x (-9) 11)
                  have b30542 := hb (x (-8) 10)
                  have b30543 := hb (x (-7) 9)
                  have b30544 := hb (x (-6) 8)
                  have b30545 := hb (x (-5) 7)
                  have b30546 := hb (x (-4) 6)
                  have b30547 := hb (x (-3) 5)
                  have b30548 := hb (x (-2) 4)
                  have b30549 := hb (x (-1) 3)
                  have b30550 := hb (x 0 2)
                  have b30551 := hb (x 1 1)
                  clear * - r30537 b30538 b30539 b30540 b30541 b30542 b30543 b30544 b30545 b30546 b30547 b30548 b30549 b30550 b30551 g2 f28586 d28663 d30368 d30344 d30436 d30456 d30476 d30496 d30516
                  omega
                have d30552 : (x (-9) 11 && x (-9) 13).toNat = 0 := by
                  have r30553 := hand1 (x (-9) 11) (x (-9) 13)
                  have b30554 := hb (x (-9) 11)
                  have b30555 := hb (x (-9) 11 && x (-9) 13)
                  clear * - r30553 b30554 b30555 d30536
                  omega
                have d30556 : (x (-10) 12).toNat = 0 := by
                  have r30557 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30558 := hb (x (-12) 14)
                  have b30559 := hb (x (-11) 13)
                  have b30560 := hb (x (-10) 12)
                  have b30561 := hb (x (-9) 11)
                  have b30562 := hb (x (-8) 10)
                  have b30563 := hb (x (-7) 9)
                  have b30564 := hb (x (-6) 8)
                  have b30565 := hb (x (-5) 7)
                  have b30566 := hb (x (-4) 6)
                  have b30567 := hb (x (-3) 5)
                  have b30568 := hb (x (-2) 4)
                  have b30569 := hb (x (-1) 3)
                  have b30570 := hb (x 0 2)
                  have b30571 := hb (x 1 1)
                  clear * - r30557 b30558 b30559 b30560 b30561 b30562 b30563 b30564 b30565 b30566 b30567 b30568 b30569 b30570 b30571 g2 f28586 d28663 d30368 d30344 d30436 d30456 d30476 d30496 d30516 d30536
                  omega
                have d30572 : (x (-10) 12 && x (-10) 14).toNat = 0 := by
                  have r30573 := hand1 (x (-10) 12) (x (-10) 14)
                  have b30574 := hb (x (-10) 12)
                  have b30575 := hb (x (-10) 12 && x (-10) 14)
                  clear * - r30573 b30574 b30575 d30556
                  omega
                have d30576 : (x (-11) 13).toNat = 0 := by
                  have r30577 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30578 := hb (x (-12) 14)
                  have b30579 := hb (x (-11) 13)
                  have b30580 := hb (x (-10) 12)
                  have b30581 := hb (x (-9) 11)
                  have b30582 := hb (x (-8) 10)
                  have b30583 := hb (x (-7) 9)
                  have b30584 := hb (x (-6) 8)
                  have b30585 := hb (x (-5) 7)
                  have b30586 := hb (x (-4) 6)
                  have b30587 := hb (x (-3) 5)
                  have b30588 := hb (x (-2) 4)
                  have b30589 := hb (x (-1) 3)
                  have b30590 := hb (x 0 2)
                  have b30591 := hb (x 1 1)
                  clear * - r30577 b30578 b30579 b30580 b30581 b30582 b30583 b30584 b30585 b30586 b30587 b30588 b30589 b30590 b30591 g2 f28586 d28663 d30368 d30344 d30436 d30456 d30476 d30496 d30516 d30536 d30556
                  omega
                have d30592 : (x (-3) 5 && x (-3) 7).toNat = 1 := by
                  have r30593 : 1 ≤ (x 2 2).toNat + (x 1 1 && x 1 3).toNat + (x 0 2 && x 0 4).toNat + (x (-1) 3 && x (-1) 5).toNat + (x (-2) 4 && x (-2) 6).toNat + (x (-3) 5 && x (-3) 7).toNat + (x (-4) 6 && x (-4) 8).toNat + (x (-5) 7 && x (-5) 9).toNat + (x (-6) 8 && x (-6) 10).toNat + (x (-7) 9 && x (-7) 11).toNat + (x (-8) 10 && x (-8) 12).toNat + (x (-9) 11 && x (-9) 13).toNat + (x (-10) 12 && x (-10) 14).toNat + (x (-11) 13).toNat := by have q := hcov2 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30594 := hb (x (-11) 13)
                  have b30595 := hb (x 2 2)
                  have b30596 := hb (x 1 1 && x 1 3)
                  have b30597 := hb (x 0 2 && x 0 4)
                  have b30598 := hb (x (-1) 3 && x (-1) 5)
                  have b30599 := hb (x (-2) 4 && x (-2) 6)
                  have b30600 := hb (x (-3) 5 && x (-3) 7)
                  have b30601 := hb (x (-4) 6 && x (-4) 8)
                  have b30602 := hb (x (-5) 7 && x (-5) 9)
                  have b30603 := hb (x (-6) 8 && x (-6) 10)
                  have b30604 := hb (x (-7) 9 && x (-7) 11)
                  have b30605 := hb (x (-8) 10 && x (-8) 12)
                  have b30606 := hb (x (-9) 11 && x (-9) 13)
                  have b30607 := hb (x (-10) 12 && x (-10) 14)
                  clear * - r30593 b30594 b30595 b30596 b30597 b30598 b30599 b30600 b30601 b30602 b30603 b30604 b30605 b30606 b30607 g8 g14 g15 d28619 d30356 d30452 d30472 d30492 d30512 d30532 d30552 d30572 d30576
                  omega
                have d30608 : (x (-3) 7).toNat = 1 := by
                  have r30609 := hand2 (x (-3) 5) (x (-3) 7)
                  have b30610 := hb (x (-3) 7)
                  have b30611 := hb (x (-3) 5 && x (-3) 7)
                  clear * - r30609 b30610 b30611 d30592
                  omega
                have d30612 : (x 4 8).toNat = 0 := by
                  have r30613 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30614 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                  have e30615 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                  have e30616 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                  have e30617 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                  have e30618 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                  have e30619 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                  have b30620 := hb (x (-3) 7)
                  have b30621 := hb (x (-2) 6)
                  have b30622 := hb (x (-1) 5)
                  have b30623 := hb (x 0 4)
                  have b30624 := hb (x 1 11)
                  have b30625 := hb (x 2 10)
                  have b30626 := hb (x 3 9)
                  have b30627 := hb (x 4 8)
                  clear * - r30613 e30614 e30615 e30616 e30617 e30618 e30619 b30620 b30621 b30622 b30623 b30624 b30625 b30626 b30627 g9 g6 g0 d28615 d30352 d30608
                  omega
                have d30628 : (x 3 9).toNat = 0 := by
                  have r30629 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30630 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
                  have e30631 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
                  have e30632 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
                  have e30633 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
                  have e30634 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
                  have e30635 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
                  have b30636 := hb (x (-3) 7)
                  have b30637 := hb (x (-2) 6)
                  have b30638 := hb (x (-1) 5)
                  have b30639 := hb (x 0 4)
                  have b30640 := hb (x 1 11)
                  have b30641 := hb (x 2 10)
                  have b30642 := hb (x 3 9)
                  have b30643 := hb (x 4 8)
                  clear * - r30629 e30630 e30631 e30632 e30633 e30634 e30635 b30636 b30637 b30638 b30639 b30640 b30641 b30642 b30643 d30612 g9 g6 g0 d28615 d30352 d30608
                  omega
                have d30644 : (x (-3) 6).toNat = 1 := by
                  have r30645 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have b30646 := hb (x (-3) 6)
                  have b30647 := hb (x 3 9)
                  have b30648 := hb (x 2 1 && x 2 10)
                  have b30649 := hb (x 1 2 && x 1 11)
                  have b30650 := hb (x 0 3 && x 0 12)
                  have b30651 := hb (x (-1) 4 && x (-1) 13)
                  have b30652 := hb (x (-2) 5 && x (-2) 14)
                  clear * - r30645 b30646 b30647 b30648 b30649 b30650 b30651 b30652 d30628 g20 g21 d28210 d28611 d30328
                  omega
                have d30653 : (x 3 8).toNat = 0 := by
                  have r30654 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                  have e30655 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
                  have e30656 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
                  have e30657 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
                  have e30658 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
                  have e30659 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
                  have e30660 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
                  have b30661 := hb (x (-4) 7)
                  have b30662 := hb (x (-3) 6)
                  have b30663 := hb (x (-2) 5)
                  have b30664 := hb (x (-1) 4)
                  have b30665 := hb (x 0 11)
                  have b30666 := hb (x 1 10)
                  have b30667 := hb (x 2 9)
                  have b30668 := hb (x 3 8)
                  clear * - r30654 e30655 e30656 e30657 e30658 e30659 e30660 b30661 b30662 b30663 b30664 b30665 b30666 b30667 b30668 d28768 g5 d28866 d30308 d30324 d30644
                  omega
                have d30669 : (x 3 8 && x 3 11).toNat = 0 := by
                  have r30670 := hand1 (x 3 8) (x 3 11)
                  have b30671 := hb (x 3 8)
                  have b30672 := hb (x 3 8 && x 3 11)
                  clear * - r30670 b30671 b30672 d30653
                  omega
                have r30673 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r30674 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := by have q := hcount 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r30675 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r30676 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e30677 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
                have e30678 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
                have e30679 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
                have e30680 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
                have e30681 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
                have e30682 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
                have r30683 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e30684 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
                have e30685 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
                have e30686 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
                have e30687 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
                have e30688 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
                have e30689 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
                have r30690 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e30691 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
                have e30692 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
                have r30693 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e30694 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
                have e30695 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
                have r30696 : 1 ≤ (x 11 3).toNat + (x 10 1 && x 10 4).toNat + (x 9 2 && x 9 5).toNat + (x 8 3 && x 8 6).toNat + (x 7 4 && x 7 7).toNat + (x 6 5 && x 6 8).toNat + (x 5 6 && x 5 9).toNat + (x 4 7 && x 4 10).toNat + (x 3 8 && x 3 11).toNat + (x 2 9 && x 2 12).toNat + (x 1 10 && x 1 13).toNat + (x 0 11 && x 0 14).toNat + (x (-1) 12).toNat := by have q := hcov3 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r30697 : 1 ≤ (x 10 10).toNat + (x 9 1 && x 9 11).toNat + (x 8 2 && x 8 12).toNat + (x 7 3 && x 7 13).toNat + (x 6 4 && x 6 14).toNat + (x 5 5).toNat := by have q := hcov10 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r30698 : 1 ≤ (x 14 10).toNat + (x 13 1 && x 13 11).toNat + (x 12 2 && x 12 12).toNat + (x 11 3 && x 11 13).toNat + (x 10 4 && x 10 14).toNat + (x 9 5).toNat := by have q := hcov10 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r30699 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r30700 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have r30701 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
                have r30702 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
                have r30703 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
                have r30704 := hand2 (x 10 1) (x 10 4)
                have r30705 := hand2 (x 9 2) (x 9 5)
                have r30706 := hand2 (x 8 3) (x 8 6)
                have r30707 := hand2 (x 7 4) (x 7 7)
                have r30708 := hand2 (x 9 1) (x 9 11)
                have r30709 := hand1 (x 8 2) (x 8 12)
                have r30710 := hand1 (x 7 3) (x 7 13)
                have r30711 := hand1 (x 13 1) (x 13 11)
                have r30712 := hand1 (x 12 2) (x 12 12)
                have r30713 := hand2 (x 11 3) (x 11 13)
                have r30714 := hand1 (x 10 4) (x 10 14)
                have r30715 := hand2 (x 12 1) (x 12 12)
                have r30716 := hand2 (x 11 2) (x 11 13)
                have r30717 := hand1 (x 10 3) (x 10 14)
                have r30718 := hand1 (x 12 1) (x 12 14)
                have b30765 := hb (x 11 1)
                linarith only [r30673, r30674, r30675, r30676, e30677, e30678, e30679, e30680, e30681, e30682, r30683, e30684, e30685, e30686, e30687, e30688, e30689, r30690, e30691, e30692, r30693, e30694, e30695, r30696, r30697, r30698, r30699, r30700, r30701, r30702, r30703, r30704, r30705, r30706, r30707, r30708, r30709, r30710, r30711, r30712, r30713, r30714, r30715, r30716, r30717, r30718, b30765, d30287, d30300, d28599, g1, f30186, d28587, g6, d30187, d28647, g9, d28796, d28627, d30628, d30332, d28691, d30612, d30388, g13, d28735, d30372, d28820, d28800, d28816, d28836, g16, d30669, d28639, g17, d28874, d28715]
            · have f30805 : (x 0 10).toNat = 1 := by rw [h28896]; rfl
              have d30806 : (x 2 8).toNat = 0 := by
                have r30807 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e30808 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                have e30809 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                have e30810 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                have e30811 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                have e30812 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                have e30813 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                have b30814 := hb (x (-5) 7)
                have b30815 := hb (x (-4) 6)
                have b30816 := hb (x (-3) 5)
                have b30817 := hb (x (-2) 4)
                have b30818 := hb (x (-1) 11)
                have b30819 := hb (x 0 10)
                have b30820 := hb (x 1 9)
                have b30821 := hb (x 2 8)
                clear * - r30807 e30808 e30809 e30810 e30811 e30812 e30813 b30814 b30815 b30816 b30817 b30818 b30819 b30820 b30821 f30805 d28679
                omega
              have d30822 : (x 1 9).toNat = 0 := by
                have r30823 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e30824 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                have e30825 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                have e30826 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                have e30827 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                have e30828 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                have e30829 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                have b30830 := hb (x (-5) 7)
                have b30831 := hb (x (-4) 6)
                have b30832 := hb (x (-3) 5)
                have b30833 := hb (x (-2) 4)
                have b30834 := hb (x (-1) 11)
                have b30835 := hb (x 0 10)
                have b30836 := hb (x 1 9)
                have b30837 := hb (x 2 8)
                clear * - r30823 e30824 e30825 e30826 e30827 e30828 e30829 b30830 b30831 b30832 b30833 b30834 b30835 b30836 b30837 d30806 f30805 d28679
                omega
              have d30838 : (x (-2) 4).toNat = 0 := by
                have r30839 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e30840 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
                have e30841 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
                have e30842 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
                have e30843 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
                have e30844 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
                have e30845 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
                have b30846 := hb (x (-5) 7)
                have b30847 := hb (x (-4) 6)
                have b30848 := hb (x (-3) 5)
                have b30849 := hb (x (-2) 4)
                have b30850 := hb (x (-1) 11)
                have b30851 := hb (x 0 10)
                have b30852 := hb (x 1 9)
                have b30853 := hb (x 2 8)
                clear * - r30839 e30840 e30841 e30842 e30843 e30844 e30845 b30846 b30847 b30848 b30849 b30850 b30851 b30852 b30853 d30806 d30822 f30805 d28679
                omega
              have d30854 : (x (-2) 4 && x (-2) 14).toNat = 0 := by
                have r30855 := hand1 (x (-2) 4) (x (-2) 14)
                have b30856 := hb (x (-2) 4)
                have b30857 := hb (x (-2) 4 && x (-2) 14)
                clear * - r30855 b30856 b30857 d30838
                omega
              have d30858 : (x (-3) 5).toNat = 1 := by
                have r30859 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b30860 := hb (x (-3) 5)
                have b30861 := hb (x 2 10)
                have b30862 := hb (x 1 1 && x 1 11)
                have b30863 := hb (x 0 2 && x 0 12)
                have b30864 := hb (x (-1) 3 && x (-1) 13)
                have b30865 := hb (x (-2) 4 && x (-2) 14)
                clear * - r30859 b30860 b30861 b30862 b30863 b30864 b30865 g9 g22 d28206 d28607 d30854
                omega
              have r30866 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30867 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
              have e30868 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
              have e30869 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
              have e30870 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
              have e30871 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
              have e30872 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
              have b30873 := hb (x (-5) 7)
              have b30874 := hb (x (-4) 6)
              have b30875 := hb (x (-3) 5)
              have b30876 := hb (x (-2) 4)
              have b30877 := hb (x (-1) 11)
              have b30878 := hb (x 0 10)
              have b30879 := hb (x 1 9)
              have b30880 := hb (x 2 8)
              linarith only [r30866, e30867, e30868, e30869, e30870, e30871, e30872, b30873, b30874, b30875, b30876, b30877, b30878, b30879, b30880, d30806, d30822, f30805, d28679, d30838, d30858]
          · have f30881 : (x 0 8).toNat = 1 := by rw [h28894]; rfl
            have d30882 : (x (-2) 10).toNat = 0 := by
              have r30883 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30884 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
              have e30885 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
              have e30886 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
              have e30887 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
              have e30888 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
              have e30889 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
              have b30890 := hb (x (-7) 7)
              have b30891 := hb (x (-6) 6)
              have b30892 := hb (x (-5) 5)
              have b30893 := hb (x (-4) 4)
              have b30894 := hb (x (-3) 11)
              have b30895 := hb (x (-2) 10)
              have b30896 := hb (x (-1) 9)
              have b30897 := hb (x 0 8)
              clear * - r30883 e30884 e30885 e30886 e30887 e30888 e30889 b30890 b30891 b30892 b30893 b30894 b30895 b30896 b30897 f30881 d28623
              omega
            have d30898 : (x (-3) 11).toNat = 0 := by
              have r30899 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e30900 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
              have e30901 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
              have e30902 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
              have e30903 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
              have e30904 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
              have e30905 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
              have b30906 := hb (x (-7) 7)
              have b30907 := hb (x (-6) 6)
              have b30908 := hb (x (-5) 5)
              have b30909 := hb (x (-4) 4)
              have b30910 := hb (x (-3) 11)
              have b30911 := hb (x (-2) 10)
              have b30912 := hb (x (-1) 9)
              have b30913 := hb (x 0 8)
              clear * - r30899 e30900 e30901 e30902 e30903 e30904 e30905 b30906 b30907 b30908 b30909 b30910 b30911 b30912 b30913 f30881 d28623 d30882
              omega
            have d30914 : (x (-3) 1 && x (-3) 11).toNat = 0 := by
              have r30915 := hand2 (x (-3) 1) (x (-3) 11)
              have b30916 := hb (x (-3) 11)
              have b30917 := hb (x (-3) 1 && x (-3) 11)
              clear * - r30915 b30916 b30917 d30898
              omega
            have r30918 : (x 1 1).toNat + (x 0 2).toNat + (x (-1) 3).toNat + (x (-2) 4).toNat + (x (-3) 5).toNat + (x (-4) 6).toNat + (x (-5) 7).toNat + (x (-6) 8).toNat + (x (-7) 9).toNat + (x (-8) 10).toNat + (x (-9) 11).toNat + (x (-10) 12).toNat + (x (-11) 13).toNat + (x (-12) 14).toNat = 3 := by have q := hcount 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r30919 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30920 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
            have e30921 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
            have e30922 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
            have e30923 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
            have e30924 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
            have e30925 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
            have r30926 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30927 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
            have e30928 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
            have r30929 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30930 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
            have e30931 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
            have r30932 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r30933 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have r30934 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
            have r30935 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
            have r30936 := hand2 (x (-2) 4) (x (-2) 8)
            have r30937 := hand2 (x (-3) 5) (x (-3) 9)
            have r30938 := hand1 (x (-4) 6) (x (-4) 10)
            have r30939 := hand1 (x (-5) 7) (x (-5) 11)
            have r30940 := hand1 (x (-6) 8) (x (-6) 12)
            have r30941 := hand1 (x (-7) 9) (x (-7) 13)
            have r30942 := hand1 (x (-4) 2) (x (-4) 12)
            have r30943 := hand1 (x (-5) 3) (x (-5) 13)
            have r30944 := hand1 (x (-6) 4) (x (-6) 14)
            have r30945 := hand1 (x (-2) 4) (x (-2) 14)
            linarith only [r30918, r30919, e30920, e30921, e30922, e30923, e30924, e30925, r30926, e30927, e30928, r30929, e30930, e30931, r30932, r30933, r30934, r30935, r30936, r30937, r30938, r30939, r30940, r30941, r30942, r30943, r30944, r30945, d30882, d28663, f28586, g2, d28659, d28643, g9, d28856, d28675, d30914, g22, d28206, d28607]
        · have f30992 : (x 0 7).toNat = 1 := by rw [h28888]; rfl
          have d30993 : (x 7 8).toNat = 0 := by
            have r30994 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e30995 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e30996 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e30997 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e30998 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e30999 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e31000 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b31001 := hb (x 0 7)
            have b31002 := hb (x 1 6)
            have b31003 := hb (x 2 5)
            have b31004 := hb (x 3 4)
            have b31005 := hb (x 4 11)
            have b31006 := hb (x 5 10)
            have b31007 := hb (x 6 9)
            have b31008 := hb (x 7 8)
            clear * - r30994 e30995 e30996 e30997 e30998 e30999 e31000 b31001 b31002 b31003 b31004 b31005 b31006 b31007 b31008 d28764 g4 f30992
            omega
          have d31009 : (x 6 9).toNat = 0 := by
            have r31010 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31011 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e31012 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e31013 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e31014 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e31015 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e31016 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b31017 := hb (x 0 7)
            have b31018 := hb (x 1 6)
            have b31019 := hb (x 2 5)
            have b31020 := hb (x 3 4)
            have b31021 := hb (x 4 11)
            have b31022 := hb (x 5 10)
            have b31023 := hb (x 6 9)
            have b31024 := hb (x 7 8)
            clear * - r31010 e31011 e31012 e31013 e31014 e31015 e31016 b31017 b31018 b31019 b31020 b31021 b31022 b31023 b31024 d30993 d28764 g4 f30992
            omega
          have d31025 : (x 5 10).toNat = 0 := by
            have r31026 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31027 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e31028 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e31029 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e31030 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e31031 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e31032 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b31033 := hb (x 0 7)
            have b31034 := hb (x 1 6)
            have b31035 := hb (x 2 5)
            have b31036 := hb (x 3 4)
            have b31037 := hb (x 4 11)
            have b31038 := hb (x 5 10)
            have b31039 := hb (x 6 9)
            have b31040 := hb (x 7 8)
            clear * - r31026 e31027 e31028 e31029 e31030 e31031 e31032 b31033 b31034 b31035 b31036 b31037 b31038 b31039 b31040 d30993 d31009 d28764 g4 f30992
            omega
          have d31041 : (x 4 11).toNat = 0 := by
            have r31042 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31043 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e31044 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e31045 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e31046 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e31047 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e31048 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b31049 := hb (x 0 7)
            have b31050 := hb (x 1 6)
            have b31051 := hb (x 2 5)
            have b31052 := hb (x 3 4)
            have b31053 := hb (x 4 11)
            have b31054 := hb (x 5 10)
            have b31055 := hb (x 6 9)
            have b31056 := hb (x 7 8)
            clear * - r31042 e31043 e31044 e31045 e31046 e31047 e31048 b31049 b31050 b31051 b31052 b31053 b31054 b31055 b31056 d30993 d31009 d31025 d28764 g4 f30992
            omega
          have d31057 : (x 3 4).toNat = 0 := by
            have r31058 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31059 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e31060 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e31061 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e31062 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e31063 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e31064 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b31065 := hb (x 0 7)
            have b31066 := hb (x 1 6)
            have b31067 := hb (x 2 5)
            have b31068 := hb (x 3 4)
            have b31069 := hb (x 4 11)
            have b31070 := hb (x 5 10)
            have b31071 := hb (x 6 9)
            have b31072 := hb (x 7 8)
            clear * - r31058 e31059 e31060 e31061 e31062 e31063 e31064 b31065 b31066 b31067 b31068 b31069 b31070 b31071 b31072 d30993 d31009 d31025 d31041 d28764 g4 f30992
            omega
          have d31073 : (x 7 11).toNat = 1 := by
            have r31074 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b31075 := hb (x 3 4)
            have b31076 := hb (x 7 11)
            have b31077 := hb (x 6 1 && x 6 12)
            have b31078 := hb (x 5 2 && x 5 13)
            have b31079 := hb (x 4 3 && x 4 14)
            clear * - r31074 b31075 b31076 b31077 b31078 b31079 d28707 d28731 g29 d31057
            omega
          have d31080 : (x 7 3).toNat = 1 := by
            have r31081 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
            have b31082 := hb (x 7 3)
            have b31083 := hb (x 7 11)
            clear * - r31081 b31082 b31083 d31073
            omega
          have d31084 : (x 10 12).toNat = 0 := by
            have r31085 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31086 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
            have e31087 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
            have b31088 := hb (x 7 3)
            have b31089 := hb (x 8 2)
            have b31090 := hb (x 9 13)
            have b31091 := hb (x 10 12)
            clear * - r31085 e31086 e31087 b31088 b31089 b31090 b31091 d31080
            omega
          have d31092 : (x 10 4).toNat = 0 := by
            have r31093 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
            have b31094 := hb (x 10 4)
            have b31095 := hb (x 10 12)
            clear * - r31093 b31094 b31095 d31084
            omega
          have d31096 : (x 10 4 && x 10 13).toNat = 0 := by
            have r31097 := hand1 (x 10 4) (x 10 13)
            have b31098 := hb (x 10 4)
            have b31099 := hb (x 10 4 && x 10 13)
            clear * - r31097 b31098 b31099 d31092
            omega
          have d31100 : (x 9 13).toNat = 0 := by
            have r31101 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31102 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
            have e31103 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
            have b31104 := hb (x 7 3)
            have b31105 := hb (x 8 2)
            have b31106 := hb (x 9 13)
            have b31107 := hb (x 10 12)
            clear * - r31101 e31102 e31103 b31104 b31105 b31106 b31107 d31084 d31080
            omega
          have d31108 : (x 9 5).toNat = 0 := by
            have r31109 : (x 9 5).toNat ≤ (x 9 13).toNat := himp _ _ (hp5 9)
            have b31110 := hb (x 9 5)
            have b31111 := hb (x 9 13)
            clear * - r31109 b31110 b31111 d31100
            omega
          have d31112 : (x 9 5 && x 9 14).toNat = 0 := by
            have r31113 := hand1 (x 9 5) (x 9 14)
            have b31114 := hb (x 9 5)
            have b31115 := hb (x 9 5 && x 9 14)
            clear * - r31113 b31114 b31115 d31108
            omega
          have d31116 : (x 8 2).toNat = 0 := by
            have r31117 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31118 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
            have e31119 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
            have b31120 := hb (x 7 3)
            have b31121 := hb (x 8 2)
            have b31122 := hb (x 9 13)
            have b31123 := hb (x 10 12)
            clear * - r31117 e31118 e31119 b31120 b31121 b31122 b31123 d31084 d31100 d31080
            omega
          have d31124 : (x 8 2 && x 8 6).toNat = 0 := by
            have r31125 := hand1 (x 8 2) (x 8 6)
            have b31126 := hb (x 8 2)
            have b31127 := hb (x 8 2 && x 8 6)
            clear * - r31125 b31126 b31127 d31116
            omega
          have d31128 : (x 8 10).toNat = 0 := by
            have r31129 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
            have b31130 := hb (x 8 2)
            have b31131 := hb (x 8 10)
            clear * - r31129 b31130 b31131 d31116
            omega
          have d31132 : (x 10 8).toNat = 0 := by
            have r31133 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31134 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e31135 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e31136 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e31137 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e31138 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e31139 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b31140 := hb (x 3 7)
            have b31141 := hb (x 4 6)
            have b31142 := hb (x 5 5)
            have b31143 := hb (x 6 4)
            have b31144 := hb (x 7 11)
            have b31145 := hb (x 8 10)
            have b31146 := hb (x 9 9)
            have b31147 := hb (x 10 8)
            clear * - r31133 e31134 e31135 e31136 e31137 e31138 e31139 b31140 b31141 b31142 b31143 b31144 b31145 b31146 b31147 d31128 d31073 d28711 d28735 g12
            omega
          have d31148 : (x 9 9).toNat = 0 := by
            have r31149 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31150 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e31151 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e31152 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e31153 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e31154 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e31155 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b31156 := hb (x 3 7)
            have b31157 := hb (x 4 6)
            have b31158 := hb (x 5 5)
            have b31159 := hb (x 6 4)
            have b31160 := hb (x 7 11)
            have b31161 := hb (x 8 10)
            have b31162 := hb (x 9 9)
            have b31163 := hb (x 10 8)
            clear * - r31149 e31150 e31151 e31152 e31153 e31154 e31155 b31156 b31157 b31158 b31159 b31160 b31161 b31162 b31163 d31132 d31128 d31073 d28711 d28735 g12
            omega
          have d31164 : (x 3 7).toNat = 0 := by
            have r31165 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e31166 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
            have e31167 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
            have e31168 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
            have e31169 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
            have e31170 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
            have e31171 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
            have b31172 := hb (x 3 7)
            have b31173 := hb (x 4 6)
            have b31174 := hb (x 5 5)
            have b31175 := hb (x 6 4)
            have b31176 := hb (x 7 11)
            have b31177 := hb (x 8 10)
            have b31178 := hb (x 9 9)
            have b31179 := hb (x 10 8)
            clear * - r31165 e31166 e31167 e31168 e31169 e31170 e31171 b31172 b31173 b31174 b31175 b31176 b31177 b31178 b31179 d31132 d31148 d31128 d31073 d28711 d28735 g12
            omega
          have d31180 : (x 3 7 && x 3 11).toNat = 0 := by
            have r31181 := hand1 (x 3 7) (x 3 11)
            have b31182 := hb (x 3 7)
            have b31183 := hb (x 3 7 && x 3 11)
            clear * - r31181 b31182 b31183 d31164
            omega
          have r31184 : (x 13 1).toNat + (x 12 2).toNat + (x 11 3).toNat + (x 10 4).toNat + (x 9 5).toNat + (x 8 6).toNat + (x 7 7).toNat + (x 6 8).toNat + (x 5 9).toNat + (x 4 10).toNat + (x 3 11).toNat + (x 2 12).toNat + (x 1 13).toNat + (x 0 14).toNat = 3 := by have q := hcount 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31185 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31186 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31187 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
          have e31188 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
          have e31189 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
          have e31190 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
          have e31191 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
          have e31192 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
          have r31193 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31194 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e31195 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e31196 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e31197 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e31198 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e31199 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have r31200 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31201 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e31202 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have r31203 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := by have q := hcov4 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31204 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
          have e31205 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
          have r31206 : 1 ≤ (x 14 9).toNat + (x 13 1 && x 13 10).toNat + (x 12 2 && x 12 11).toNat + (x 11 3 && x 11 12).toNat + (x 10 4 && x 10 13).toNat + (x 9 5 && x 9 14).toNat + (x 8 6).toNat := by have q := hcov9 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31207 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31208 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r31209 := hand2 (x 7 3) (x 7 7)
          have r31210 := hand2 (x 13 1) (x 13 10)
          have r31211 := hand2 (x 12 2) (x 12 11)
          have r31212 := hand1 (x 11 3) (x 11 12)
          have r31213 := hand1 (x (-2) 4) (x (-2) 14)
          have r31214 := hand1 (x 13 1) (x 13 14)
          have b31253 := hb (x 14 1)
          linarith only [r31184, r31185, r31186, e31187, e31188, e31189, e31190, e31191, e31192, r31193, e31194, e31195, e31196, e31197, e31198, e31199, r31200, e31201, e31202, r31203, e31204, e31205, r31206, r31207, r31208, r31209, r31210, r31211, r31212, r31213, r31214, b31253, d28679, d28587, d28647, g7, g9, d28627, d28760, d28691, d28878, g13, d31041, d28820, d31025, d28800, d31009, d30993, d31108, d31092, d31124, d28719, d28739, g18, d31180, d28635, d28655, d31096, d31112, g22, d28206, d28607]
      · have f31276 : (x 0 5).toNat = 1 := by rw [h28886]; rfl
        have d31277 : (x 0 13).toNat = 1 := by
          have r31278 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
          have b31279 := hb (x 0 5)
          have b31280 := hb (x 0 13)
          clear * - r31278 b31279 b31280 f31276
          omega
        have d31281 : (x 1 12).toNat = 0 := by
          have r31282 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31283 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e31284 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b31285 := hb (x (-2) 3)
          have b31286 := hb (x (-1) 2)
          have b31287 := hb (x 0 13)
          have b31288 := hb (x 1 12)
          clear * - r31282 e31283 e31284 b31285 b31286 b31287 b31288 d31277
          omega
        have d31289 : (x 1 4).toNat = 0 := by
          have r31290 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
          have b31291 := hb (x 1 4)
          have b31292 := hb (x 1 12)
          clear * - r31290 b31291 b31292 d31281
          omega
        have d31293 : (x (-1) 2).toNat = 0 := by
          have r31294 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31295 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e31296 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b31297 := hb (x (-2) 3)
          have b31298 := hb (x (-1) 2)
          have b31299 := hb (x 0 13)
          have b31300 := hb (x 1 12)
          clear * - r31294 e31295 e31296 b31297 b31298 b31299 b31300 d31281 d31277
          omega
        have d31301 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
          have r31302 := hand1 (x (-1) 2) (x (-1) 12)
          have b31303 := hb (x (-1) 2)
          have b31304 := hb (x (-1) 2 && x (-1) 12)
          clear * - r31302 b31303 b31304 d31293
          omega
        have d31305 : (x (-2) 3).toNat = 0 := by
          have r31306 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31307 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e31308 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have b31309 := hb (x (-2) 3)
          have b31310 := hb (x (-1) 2)
          have b31311 := hb (x 0 13)
          have b31312 := hb (x 1 12)
          clear * - r31306 e31307 e31308 b31309 b31310 b31311 b31312 d31281 d31277 d31293
          omega
        have d31313 : (x (-2) 3 && x (-2) 14).toNat = 0 := by
          have r31314 := hand1 (x (-2) 3) (x (-2) 14)
          have b31315 := hb (x (-2) 3)
          have b31316 := hb (x (-2) 3 && x (-2) 14)
          clear * - r31314 b31315 b31316 d31305
          omega
        have d31317 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
          have r31318 := hand1 (x (-2) 3) (x (-2) 13)
          have b31319 := hb (x (-2) 3)
          have b31320 := hb (x (-2) 3 && x (-2) 13)
          clear * - r31318 b31319 b31320 d31305
          omega
        have d31321 : (x (-3) 4).toNat = 1 := by
          have r31322 : 1 ≤ (x 1 11).toNat + (x 0 1 && x 0 12).toNat + (x (-1) 2 && x (-1) 13).toNat + (x (-2) 3 && x (-2) 14).toNat + (x (-3) 4).toNat := by have q := hcov11 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31323 := hb (x (-3) 4)
          have b31324 := hb (x 1 11)
          have b31325 := hb (x 0 1 && x 0 12)
          have b31326 := hb (x (-1) 2 && x (-1) 13)
          have b31327 := hb (x (-2) 3 && x (-2) 14)
          clear * - r31322 b31323 b31324 b31325 b31326 b31327 g6 d28202 d28603 d31313
          omega
        have d31328 : (x (-3) 12).toNat = 1 := by
          have r31329 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
          have b31330 := hb (x (-3) 4)
          have b31331 := hb (x (-3) 12)
          clear * - r31329 b31330 b31331 d31321
          omega
        have d31332 : (x (-4) 13).toNat = 0 := by
          have r31333 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31334 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e31335 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b31336 := hb (x (-6) 3)
          have b31337 := hb (x (-5) 2)
          have b31338 := hb (x (-4) 13)
          have b31339 := hb (x (-3) 12)
          clear * - r31333 e31334 e31335 b31336 b31337 b31338 b31339 d31328
          omega
        have d31340 : (x (-4) 5).toNat = 0 := by
          have r31341 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
          have b31342 := hb (x (-4) 5)
          have b31343 := hb (x (-4) 13)
          clear * - r31341 b31342 b31343 d31332
          omega
        have d31344 : (x (-5) 2).toNat = 0 := by
          have r31345 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31346 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
          have e31347 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
          have b31348 := hb (x (-6) 3)
          have b31349 := hb (x (-5) 2)
          have b31350 := hb (x (-4) 13)
          have b31351 := hb (x (-3) 12)
          clear * - r31345 e31346 e31347 b31348 b31349 b31350 b31351 d31328 d31332
          omega
        have d31352 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
          have r31353 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31354 := hb (x (-4) 5)
          have b31355 := hb (x 1 10)
          have b31356 := hb (x 0 1 && x 0 11)
          have b31357 := hb (x (-1) 2 && x (-1) 12)
          have b31358 := hb (x (-2) 3 && x (-2) 13)
          have b31359 := hb (x (-3) 4 && x (-3) 14)
          clear * - r31353 b31354 b31355 b31356 b31357 b31358 b31359 g5 d28870 d31301 d31317 d31340
          omega
        have d31360 : (x (-3) 14).toNat = 1 := by
          have r31361 := hand2 (x (-3) 4) (x (-3) 14)
          have b31362 := hb (x (-3) 14)
          have b31363 := hb (x (-3) 4 && x (-3) 14)
          clear * - r31361 b31362 b31363 d31352
          omega
        have d31364 : (x (-4) 1).toNat = 0 := by
          have r31365 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31366 := hb (x (-4) 1)
          have b31367 := hb (x (-3) 14)
          clear * - r31365 b31366 b31367 d31360
          omega
        have d31368 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
          have r31369 := hand1 (x (-4) 1) (x (-4) 14)
          have b31370 := hb (x (-4) 1)
          have b31371 := hb (x (-4) 1 && x (-4) 14)
          clear * - r31369 b31370 b31371 d31364
          omega
        have d31372 : (x (-3) 13).toNat = 1 := by
          have r31373 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31374 := hb (x (-5) 2)
          have b31375 := hb (x (-3) 13)
          have b31376 := hb (x (-4) 1 && x (-4) 14)
          clear * - r31373 b31374 b31375 b31376 d31368 d31344
          omega
        have d31377 : (x (-3) 1).toNat = 1 := by
          have r31378 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
          have b31379 := hb (x (-3) 1)
          have b31380 := hb (x (-3) 13)
          clear * - r31378 b31379 b31380 d31372
          omega
        have d31381 : (x (-2) 14).toNat = 0 := by
          have r31382 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31383 := hb (x (-3) 1)
          have b31384 := hb (x (-2) 14)
          clear * - r31382 b31383 b31384 d31377
          omega
        have d31385 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
          have r31386 := hand2 (x (-2) 1) (x (-2) 14)
          have b31387 := hb (x (-2) 14)
          have b31388 := hb (x (-2) 1 && x (-2) 14)
          clear * - r31386 b31387 b31388 d31381
          omega
        have d31389 : (x (-3) 2).toNat = 1 := by
          have r31390 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31391 := hb (x (-3) 2)
          have b31392 := hb (x (-1) 13)
          have b31393 := hb (x (-2) 1 && x (-2) 14)
          clear * - r31390 b31391 b31392 b31393 d28599 d31385
          omega
        have d31394 : (x (-1) 12).toNat = 0 := by
          have r31395 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31396 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e31397 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b31398 := hb (x (-4) 3)
          have b31399 := hb (x (-3) 2)
          have b31400 := hb (x (-2) 13)
          have b31401 := hb (x (-1) 12)
          clear * - r31395 e31396 e31397 b31398 b31399 b31400 b31401 d31389
          omega
        have d31402 : (x (-1) 4).toNat = 0 := by
          have r31403 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
          have b31404 := hb (x (-1) 4)
          have b31405 := hb (x (-1) 12)
          clear * - r31403 b31404 b31405 d31394
          omega
        have d31406 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
          have r31407 := hand1 (x (-1) 4) (x (-1) 14)
          have b31408 := hb (x (-1) 4)
          have b31409 := hb (x (-1) 4 && x (-1) 14)
          clear * - r31407 b31408 b31409 d31402
          omega
        have d31410 : (x (-2) 13).toNat = 0 := by
          have r31411 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e31412 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e31413 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b31414 := hb (x (-4) 3)
          have b31415 := hb (x (-3) 2)
          have b31416 := hb (x (-2) 13)
          have b31417 := hb (x (-1) 12)
          clear * - r31411 e31412 e31413 b31414 b31415 b31416 b31417 d31394 d31389
          omega
        have d31418 : (x (-2) 5).toNat = 0 := by
          have r31419 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
          have b31420 := hb (x (-2) 5)
          have b31421 := hb (x (-2) 13)
          clear * - r31419 b31420 b31421 d31410
          omega
        have d31422 : (x 3 10).toNat = 1 := by
          have r31423 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b31424 := hb (x (-2) 5)
          have b31425 := hb (x 3 10)
          have b31426 := hb (x 2 1 && x 2 11)
          have b31427 := hb (x 1 2 && x 1 12)
          have b31428 := hb (x 0 3 && x 0 13)
          have b31429 := hb (x (-1) 4 && x (-1) 14)
          clear * - r31423 b31424 b31425 b31426 b31427 b31428 b31429 d28756 g23 d28862 d31406 d31418
          omega
        have r31430 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31431 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
        have e31432 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
        have e31433 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
        have e31434 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
        have e31435 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
        have e31436 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
        have b31437 := hb (x (-2) 7)
        have b31438 := hb (x (-1) 6)
        have b31439 := hb (x 0 5)
        have b31440 := hb (x 1 4)
        have b31441 := hb (x 2 11)
        have b31442 := hb (x 3 10)
        have b31443 := hb (x 4 9)
        have b31444 := hb (x 5 8)
        linarith only [r31430, e31431, e31432, e31433, e31434, e31435, e31436, b31437, b31438, b31439, b31440, b31441, b31442, b31443, b31444, d31422, d28796, d31289, f31276]
    · have f31445 : (x 0 3).toNat = 1 := by rw [h28860]; rfl
      have d31446 : (x 3 12).toNat = 0 := by
        have r31447 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31448 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e31449 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b31450 := hb (x 0 3)
        have b31451 := hb (x 1 2)
        have b31452 := hb (x 2 13)
        have b31453 := hb (x 3 12)
        clear * - r31447 e31448 e31449 b31450 b31451 b31452 b31453 d28760 g3 f31445
        omega
      have d31454 : (x 3 1 && x 3 12).toNat = 0 := by
        have r31455 := hand2 (x 3 1) (x 3 12)
        have b31456 := hb (x 3 12)
        have b31457 := hb (x 3 1 && x 3 12)
        clear * - r31455 b31456 b31457 d31446
        omega
      have d31458 : (x 3 4).toNat = 0 := by
        have r31459 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
        have b31460 := hb (x 3 4)
        have b31461 := hb (x 3 12)
        clear * - r31459 b31460 b31461 d31446
        omega
      have d31462 : (x 7 11).toNat = 1 := by
        have r31463 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31464 := hb (x 3 4)
        have b31465 := hb (x 7 11)
        have b31466 := hb (x 6 1 && x 6 12)
        have b31467 := hb (x 5 2 && x 5 13)
        have b31468 := hb (x 4 3 && x 4 14)
        clear * - r31463 b31464 b31465 b31466 b31467 b31468 d28707 d28731 g29 d31458
        omega
      have d31469 : (x 7 3).toNat = 1 := by
        have r31470 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
        have b31471 := hb (x 7 3)
        have b31472 := hb (x 7 11)
        clear * - r31470 b31471 b31472 d31462
        omega
      have d31473 : (x 10 12).toNat = 0 := by
        have r31474 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31475 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e31476 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b31477 := hb (x 7 3)
        have b31478 := hb (x 8 2)
        have b31479 := hb (x 9 13)
        have b31480 := hb (x 10 12)
        clear * - r31474 e31475 e31476 b31477 b31478 b31479 b31480 d31469
        omega
      have d31481 : (x 10 1 && x 10 12).toNat = 0 := by
        have r31482 := hand2 (x 10 1) (x 10 12)
        have b31483 := hb (x 10 12)
        have b31484 := hb (x 10 1 && x 10 12)
        clear * - r31482 b31483 b31484 d31473
        omega
      have d31485 : (x 9 13).toNat = 0 := by
        have r31486 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31487 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e31488 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b31489 := hb (x 7 3)
        have b31490 := hb (x 8 2)
        have b31491 := hb (x 9 13)
        have b31492 := hb (x 10 12)
        clear * - r31486 e31487 e31488 b31489 b31490 b31491 b31492 d31473 d31469
        omega
      have d31493 : (x 9 2 && x 9 13).toNat = 0 := by
        have r31494 := hand2 (x 9 2) (x 9 13)
        have b31495 := hb (x 9 13)
        have b31496 := hb (x 9 2 && x 9 13)
        clear * - r31494 b31495 b31496 d31485
        omega
      have d31497 : (x 8 2).toNat = 0 := by
        have r31498 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31499 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
        have e31500 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
        have b31501 := hb (x 7 3)
        have b31502 := hb (x 8 2)
        have b31503 := hb (x 9 13)
        have b31504 := hb (x 10 12)
        clear * - r31498 e31499 e31500 b31501 b31502 b31503 b31504 d31473 d31485 d31469
        omega
      have d31505 : (x 4 11).toNat = 1 := by
        have r31506 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31507 := hb (x 0 4)
        have b31508 := hb (x 4 11)
        have b31509 := hb (x 3 1 && x 3 12)
        have b31510 := hb (x 2 2 && x 2 13)
        have b31511 := hb (x 1 3 && x 1 14)
        clear * - r31506 b31507 b31508 b31509 b31510 b31511 d31454 g27 g28 g0
        omega
      have d31512 : (x 4 3).toNat = 1 := by
        have r31513 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
        have b31514 := hb (x 4 3)
        have b31515 := hb (x 4 11)
        clear * - r31513 b31514 b31515 d31505
        omega
      have d31516 : (x 7 12).toNat = 0 := by
        have r31517 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31518 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e31519 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b31520 := hb (x 4 3)
        have b31521 := hb (x 5 2)
        have b31522 := hb (x 6 13)
        have b31523 := hb (x 7 12)
        clear * - r31517 e31518 e31519 b31520 b31521 b31522 b31523 d31512
        omega
      have d31524 : (x 7 1 && x 7 12).toNat = 0 := by
        have r31525 := hand2 (x 7 1) (x 7 12)
        have b31526 := hb (x 7 12)
        have b31527 := hb (x 7 1 && x 7 12)
        clear * - r31525 b31526 b31527 d31516
        omega
      have d31528 : (x 7 4).toNat = 0 := by
        have r31529 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
        have b31530 := hb (x 7 4)
        have b31531 := hb (x 7 12)
        clear * - r31529 b31530 b31531 d31516
        omega
      have d31532 : (x 6 13).toNat = 0 := by
        have r31533 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31534 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e31535 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b31536 := hb (x 4 3)
        have b31537 := hb (x 5 2)
        have b31538 := hb (x 6 13)
        have b31539 := hb (x 7 12)
        clear * - r31533 e31534 e31535 b31536 b31537 b31538 b31539 d31516 d31512
        omega
      have d31540 : (x 6 2 && x 6 13).toNat = 0 := by
        have r31541 := hand2 (x 6 2) (x 6 13)
        have b31542 := hb (x 6 13)
        have b31543 := hb (x 6 2 && x 6 13)
        clear * - r31541 b31542 b31543 d31532
        omega
      have d31544 : (x 5 1 && x 5 14).toNat = 1 := by
        have r31545 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31546 := hb (x 4 2)
        have b31547 := hb (x 6 13)
        have b31548 := hb (x 5 1 && x 5 14)
        clear * - r31545 b31546 b31547 b31548 d31532 g10
        omega
      have d31549 : (x 5 1).toNat = 1 := by
        have r31550 := hand1 (x 5 1) (x 5 14)
        have b31551 := hb (x 5 1)
        have b31552 := hb (x 5 1 && x 5 14)
        clear * - r31550 b31551 b31552 d31544
        omega
      have d31553 : (x 6 14).toNat = 0 := by
        have r31554 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31555 := hb (x 5 1)
        have b31556 := hb (x 6 14)
        clear * - r31554 b31555 b31556 d31549
        omega
      have d31557 : (x 6 1 && x 6 14).toNat = 0 := by
        have r31558 := hand2 (x 6 1) (x 6 14)
        have b31559 := hb (x 6 14)
        have b31560 := hb (x 6 1 && x 6 14)
        clear * - r31558 b31559 b31560 d31553
        omega
      have d31561 : (x 6 2).toNat = 0 := by
        have r31562 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
        have b31563 := hb (x 6 2)
        have b31564 := hb (x 6 14)
        clear * - r31562 b31563 b31564 d31553
        omega
      have d31565 : (x 5 2).toNat = 0 := by
        have r31566 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31567 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
        have e31568 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
        have b31569 := hb (x 4 3)
        have b31570 := hb (x 5 2)
        have b31571 := hb (x 6 13)
        have b31572 := hb (x 7 12)
        clear * - r31566 e31567 e31568 b31569 b31570 b31571 b31572 d31516 d31532 d31512
        omega
      have d31573 : (x 7 13).toNat = 1 := by
        have r31574 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31575 := hb (x 5 2)
        have b31576 := hb (x 7 13)
        have b31577 := hb (x 6 1 && x 6 14)
        clear * - r31574 b31575 b31576 b31577 d31557 d31565
        omega
      have d31578 : (x 7 1).toNat = 1 := by
        have r31579 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
        have b31580 := hb (x 7 1)
        have b31581 := hb (x 7 13)
        clear * - r31579 b31580 b31581 d31573
        omega
      have d31582 : (x 8 14).toNat = 0 := by
        have r31583 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31584 := hb (x 7 1)
        have b31585 := hb (x 8 14)
        clear * - r31583 b31584 b31585 d31578
        omega
      have d31586 : (x 8 3 && x 8 14).toNat = 0 := by
        have r31587 := hand2 (x 8 3) (x 8 14)
        have b31588 := hb (x 8 14)
        have b31589 := hb (x 8 3 && x 8 14)
        clear * - r31587 b31588 b31589 d31582
        omega
      have d31590 : (x 11 11).toNat = 1 := by
        have r31591 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31592 := hb (x 7 4)
        have b31593 := hb (x 11 11)
        have b31594 := hb (x 10 1 && x 10 12)
        have b31595 := hb (x 9 2 && x 9 13)
        have b31596 := hb (x 8 3 && x 8 14)
        clear * - r31591 b31592 b31593 b31594 b31595 b31596 d31481 d31493 d31586 d31528
        omega
      have d31597 : (x 11 3).toNat = 1 := by
        have r31598 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
        have b31599 := hb (x 11 3)
        have b31600 := hb (x 11 11)
        clear * - r31598 b31599 b31600 d31590
        omega
      have d31601 : (x 14 12).toNat = 0 := by
        have r31602 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31603 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e31604 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b31605 := hb (x 11 3)
        have b31606 := hb (x 12 2)
        have b31607 := hb (x 13 13)
        have b31608 := hb (x 14 12)
        clear * - r31602 e31603 e31604 b31605 b31606 b31607 b31608 d31597
        omega
      have d31609 : (x 14 1 && x 14 12).toNat = 0 := by
        have r31610 := hand2 (x 14 1) (x 14 12)
        have b31611 := hb (x 14 12)
        have b31612 := hb (x 14 1 && x 14 12)
        clear * - r31610 b31611 b31612 d31601
        omega
      have d31613 : (x 13 13).toNat = 0 := by
        have r31614 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31615 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e31616 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b31617 := hb (x 11 3)
        have b31618 := hb (x 12 2)
        have b31619 := hb (x 13 13)
        have b31620 := hb (x 14 12)
        clear * - r31614 e31615 e31616 b31617 b31618 b31619 b31620 d31601 d31597
        omega
      have d31621 : (x 13 2 && x 13 13).toNat = 0 := by
        have r31622 := hand2 (x 13 2) (x 13 13)
        have b31623 := hb (x 13 13)
        have b31624 := hb (x 13 2 && x 13 13)
        clear * - r31622 b31623 b31624 d31613
        omega
      have d31625 : (x 12 2).toNat = 0 := by
        have r31626 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31627 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e31628 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b31629 := hb (x 11 3)
        have b31630 := hb (x 12 2)
        have b31631 := hb (x 13 13)
        have b31632 := hb (x 14 12)
        clear * - r31626 e31627 e31628 b31629 b31630 b31631 b31632 d31601 d31613 d31597
        omega
      have d31633 : (x 8 12).toNat = 0 := by
        have r31634 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31635 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e31636 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b31637 := hb (x 5 3)
        have b31638 := hb (x 6 2)
        have b31639 := hb (x 7 13)
        have b31640 := hb (x 8 12)
        clear * - r31634 e31635 e31636 b31637 b31638 b31639 b31640 d31573 d31561
        omega
      have d31641 : (x 8 4).toNat = 0 := by
        have r31642 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
        have b31643 := hb (x 8 4)
        have b31644 := hb (x 8 12)
        clear * - r31642 b31643 b31644 d31633
        omega
      have d31645 : (x 5 3).toNat = 0 := by
        have r31646 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31647 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e31648 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b31649 := hb (x 5 3)
        have b31650 := hb (x 6 2)
        have b31651 := hb (x 7 13)
        have b31652 := hb (x 8 12)
        clear * - r31646 e31647 e31648 b31649 b31650 b31651 b31652 d31633 d31573 d31561
        omega
      have d31653 : (x 5 3 && x 5 14).toNat = 0 := by
        have r31654 := hand1 (x 5 3) (x 5 14)
        have b31655 := hb (x 5 3)
        have b31656 := hb (x 5 3 && x 5 14)
        clear * - r31654 b31655 b31656 d31645
        omega
      have d31657 : (x 8 11).toNat = 1 := by
        have r31658 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31659 := hb (x 4 4)
        have b31660 := hb (x 8 11)
        have b31661 := hb (x 7 1 && x 7 12)
        have b31662 := hb (x 6 2 && x 6 13)
        have b31663 := hb (x 5 3 && x 5 14)
        clear * - r31658 b31659 b31660 b31661 b31662 b31663 d31524 d31540 d31653 g11
        omega
      have d31664 : (x 8 3).toNat = 1 := by
        have r31665 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b31666 := hb (x 8 3)
        have b31667 := hb (x 8 11)
        clear * - r31665 b31666 b31667 d31657
        omega
      have d31668 : (x 11 12).toNat = 0 := by
        have r31669 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31670 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e31671 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b31672 := hb (x 8 3)
        have b31673 := hb (x 9 2)
        have b31674 := hb (x 10 13)
        have b31675 := hb (x 11 12)
        clear * - r31669 e31670 e31671 b31672 b31673 b31674 b31675 d31664
        omega
      have d31676 : (x 11 1 && x 11 12).toNat = 0 := by
        have r31677 := hand2 (x 11 1) (x 11 12)
        have b31678 := hb (x 11 12)
        have b31679 := hb (x 11 1 && x 11 12)
        clear * - r31677 b31678 b31679 d31668
        omega
      have d31680 : (x 11 4).toNat = 0 := by
        have r31681 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
        have b31682 := hb (x 11 4)
        have b31683 := hb (x 11 12)
        clear * - r31681 b31682 b31683 d31668
        omega
      have d31684 : (x 10 13).toNat = 0 := by
        have r31685 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31686 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e31687 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b31688 := hb (x 8 3)
        have b31689 := hb (x 9 2)
        have b31690 := hb (x 10 13)
        have b31691 := hb (x 11 12)
        clear * - r31685 e31686 e31687 b31688 b31689 b31690 b31691 d31668 d31664
        omega
      have d31692 : (x 10 2 && x 10 13).toNat = 0 := by
        have r31693 := hand2 (x 10 2) (x 10 13)
        have b31694 := hb (x 10 13)
        have b31695 := hb (x 10 2 && x 10 13)
        clear * - r31693 b31694 b31695 d31684
        omega
      have d31696 : (x 9 1 && x 9 14).toNat = 1 := by
        have r31697 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31698 := hb (x 8 2)
        have b31699 := hb (x 10 13)
        have b31700 := hb (x 9 1 && x 9 14)
        clear * - r31697 b31698 b31699 b31700 d31684 d31497
        omega
      have d31701 : (x 9 1).toNat = 1 := by
        have r31702 := hand1 (x 9 1) (x 9 14)
        have b31703 := hb (x 9 1)
        have b31704 := hb (x 9 1 && x 9 14)
        clear * - r31702 b31703 b31704 d31696
        omega
      have d31705 : (x 10 14).toNat = 0 := by
        have r31706 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31707 := hb (x 9 1)
        have b31708 := hb (x 10 14)
        clear * - r31706 b31707 b31708 d31701
        omega
      have d31709 : (x 10 1 && x 10 14).toNat = 0 := by
        have r31710 := hand2 (x 10 1) (x 10 14)
        have b31711 := hb (x 10 14)
        have b31712 := hb (x 10 1 && x 10 14)
        clear * - r31710 b31711 b31712 d31705
        omega
      have d31713 : (x 10 2).toNat = 0 := by
        have r31714 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
        have b31715 := hb (x 10 2)
        have b31716 := hb (x 10 14)
        clear * - r31714 b31715 b31716 d31705
        omega
      have d31717 : (x 9 2).toNat = 0 := by
        have r31718 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31719 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e31720 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b31721 := hb (x 8 3)
        have b31722 := hb (x 9 2)
        have b31723 := hb (x 10 13)
        have b31724 := hb (x 11 12)
        clear * - r31718 e31719 e31720 b31721 b31722 b31723 b31724 d31668 d31684 d31664
        omega
      have d31725 : (x 11 13).toNat = 1 := by
        have r31726 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31727 := hb (x 9 2)
        have b31728 := hb (x 11 13)
        have b31729 := hb (x 10 1 && x 10 14)
        clear * - r31726 b31727 b31728 b31729 d31709 d31717
        omega
      have d31730 : (x 11 1).toNat = 1 := by
        have r31731 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
        have b31732 := hb (x 11 1)
        have b31733 := hb (x 11 13)
        clear * - r31731 b31732 b31733 d31725
        omega
      have d31734 : (x 12 14).toNat = 0 := by
        have r31735 : (x 12 14).toNat + (x 11 1).toNat = 1 := by have q := hd14 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31736 := hb (x 11 1)
        have b31737 := hb (x 12 14)
        clear * - r31735 b31736 b31737 d31730
        omega
      have d31738 : (x 12 1 && x 12 14).toNat = 0 := by
        have r31739 := hand2 (x 12 1) (x 12 14)
        have b31740 := hb (x 12 14)
        have b31741 := hb (x 12 1 && x 12 14)
        clear * - r31739 b31740 b31741 d31734
        omega
      have d31742 : (x 11 2).toNat = 1 := by
        have r31743 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31744 := hb (x 11 2)
        have b31745 := hb (x 13 13)
        have b31746 := hb (x 12 1 && x 12 14)
        clear * - r31743 b31744 b31745 b31746 d31613 d31738
        omega
      have d31747 : (x 13 12).toNat = 0 := by
        have r31748 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31749 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e31750 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b31751 := hb (x 10 3)
        have b31752 := hb (x 11 2)
        have b31753 := hb (x 12 13)
        have b31754 := hb (x 13 12)
        clear * - r31748 e31749 e31750 b31751 b31752 b31753 b31754 d31742
        omega
      have d31755 : (x 13 4).toNat = 0 := by
        have r31756 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
        have b31757 := hb (x 13 4)
        have b31758 := hb (x 13 12)
        clear * - r31756 b31757 b31758 d31747
        omega
      have d31759 : (x 13 4 && x 13 14).toNat = 0 := by
        have r31760 := hand1 (x 13 4) (x 13 14)
        have b31761 := hb (x 13 4)
        have b31762 := hb (x 13 4 && x 13 14)
        clear * - r31760 b31761 b31762 d31755
        omega
      have d31763 : (x 12 13).toNat = 0 := by
        have r31764 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31765 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e31766 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b31767 := hb (x 10 3)
        have b31768 := hb (x 11 2)
        have b31769 := hb (x 12 13)
        have b31770 := hb (x 13 12)
        clear * - r31764 e31765 e31766 b31767 b31768 b31769 b31770 d31747 d31742
        omega
      have d31771 : (x 12 5).toNat = 0 := by
        have r31772 : (x 12 5).toNat ≤ (x 12 13).toNat := himp _ _ (hp5 12)
        have b31773 := hb (x 12 5)
        have b31774 := hb (x 12 13)
        clear * - r31772 b31773 b31774 d31763
        omega
      have d31775 : (x 12 3 && x 12 14).toNat = 0 := by
        have r31776 := hand2 (x 12 3) (x 12 14)
        have b31777 := hb (x 12 14)
        have b31778 := hb (x 12 3 && x 12 14)
        clear * - r31776 b31777 b31778 d31734
        omega
      have d31779 : (x 15 11).toNat = 1 := by
        have r31780 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31781 := hb (x 11 4)
        have b31782 := hb (x 15 11)
        have b31783 := hb (x 14 1 && x 14 12)
        have b31784 := hb (x 13 2 && x 13 13)
        have b31785 := hb (x 12 3 && x 12 14)
        clear * - r31780 b31781 b31782 b31783 b31784 b31785 d31609 d31621 d31775 d31680
        omega
      have d31786 : (x 15 3).toNat = 1 := by
        have r31787 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
        have b31788 := hb (x 15 3)
        have b31789 := hb (x 15 11)
        clear * - r31787 b31788 b31789 d31779
        omega
      have d31790 : (x 18 12).toNat = 0 := by
        have r31791 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31792 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
        have e31793 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
        have b31794 := hb (x 15 3)
        have b31795 := hb (x 16 2)
        have b31796 := hb (x 17 13)
        have b31797 := hb (x 18 12)
        clear * - r31791 e31792 e31793 b31794 b31795 b31796 b31797 d31786
        omega
      have d31798 : (x 17 13).toNat = 0 := by
        have r31799 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31800 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
        have e31801 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
        have b31802 := hb (x 15 3)
        have b31803 := hb (x 16 2)
        have b31804 := hb (x 17 13)
        have b31805 := hb (x 18 12)
        clear * - r31799 e31800 e31801 b31802 b31803 b31804 b31805 d31790 d31786
        omega
      have d31806 : (x 16 2).toNat = 0 := by
        have r31807 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31808 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
        have e31809 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
        have b31810 := hb (x 15 3)
        have b31811 := hb (x 16 2)
        have b31812 := hb (x 17 13)
        have b31813 := hb (x 18 12)
        clear * - r31807 e31808 e31809 b31810 b31811 b31812 b31813 d31790 d31798 d31786
        omega
      have d31814 : (x 12 12).toNat = 0 := by
        have r31815 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31816 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e31817 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b31818 := hb (x 9 3)
        have b31819 := hb (x 10 2)
        have b31820 := hb (x 11 13)
        have b31821 := hb (x 12 12)
        clear * - r31815 e31816 e31817 b31818 b31819 b31820 b31821 d31725 d31713
        omega
      have d31822 : (x 12 4).toNat = 0 := by
        have r31823 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
        have b31824 := hb (x 12 4)
        have b31825 := hb (x 12 12)
        clear * - r31823 b31824 b31825 d31814
        omega
      have d31826 : (x 9 3).toNat = 0 := by
        have r31827 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31828 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e31829 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b31830 := hb (x 9 3)
        have b31831 := hb (x 10 2)
        have b31832 := hb (x 11 13)
        have b31833 := hb (x 12 12)
        clear * - r31827 e31828 e31829 b31830 b31831 b31832 b31833 d31814 d31725 d31713
        omega
      have d31834 : (x 9 3 && x 9 14).toNat = 0 := by
        have r31835 := hand1 (x 9 3) (x 9 14)
        have b31836 := hb (x 9 3)
        have b31837 := hb (x 9 3 && x 9 14)
        clear * - r31835 b31836 b31837 d31826
        omega
      have d31838 : (x 12 11).toNat = 1 := by
        have r31839 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31840 := hb (x 8 4)
        have b31841 := hb (x 12 11)
        have b31842 := hb (x 11 1 && x 11 12)
        have b31843 := hb (x 10 2 && x 10 13)
        have b31844 := hb (x 9 3 && x 9 14)
        clear * - r31839 b31840 b31841 b31842 b31843 b31844 d31676 d31692 d31834 d31641
        omega
      have d31845 : (x 12 3).toNat = 1 := by
        have r31846 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
        have b31847 := hb (x 12 3)
        have b31848 := hb (x 12 11)
        clear * - r31846 b31847 b31848 d31838
        omega
      have d31849 : (x 15 12).toNat = 0 := by
        have r31850 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31851 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e31852 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b31853 := hb (x 12 3)
        have b31854 := hb (x 13 2)
        have b31855 := hb (x 14 13)
        have b31856 := hb (x 15 12)
        clear * - r31850 e31851 e31852 b31853 b31854 b31855 b31856 d31845
        omega
      have d31857 : (x 15 1 && x 15 12).toNat = 0 := by
        have r31858 := hand2 (x 15 1) (x 15 12)
        have b31859 := hb (x 15 12)
        have b31860 := hb (x 15 1 && x 15 12)
        clear * - r31858 b31859 b31860 d31849
        omega
      have d31861 : (x 15 2 && x 15 12).toNat = 0 := by
        have r31862 := hand2 (x 15 2) (x 15 12)
        have b31863 := hb (x 15 12)
        have b31864 := hb (x 15 2 && x 15 12)
        clear * - r31862 b31863 b31864 d31849
        omega
      have d31865 : (x 14 13).toNat = 0 := by
        have r31866 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31867 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e31868 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b31869 := hb (x 12 3)
        have b31870 := hb (x 13 2)
        have b31871 := hb (x 14 13)
        have b31872 := hb (x 15 12)
        clear * - r31866 e31867 e31868 b31869 b31870 b31871 b31872 d31849 d31845
        omega
      have d31873 : (x 14 2 && x 14 13).toNat = 0 := by
        have r31874 := hand2 (x 14 2) (x 14 13)
        have b31875 := hb (x 14 13)
        have b31876 := hb (x 14 2 && x 14 13)
        clear * - r31874 b31875 b31876 d31865
        omega
      have d31877 : (x 14 3 && x 14 13).toNat = 0 := by
        have r31878 := hand2 (x 14 3) (x 14 13)
        have b31879 := hb (x 14 13)
        have b31880 := hb (x 14 3 && x 14 13)
        clear * - r31878 b31879 b31880 d31865
        omega
      have d31881 : (x 13 1 && x 13 14).toNat = 1 := by
        have r31882 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31883 := hb (x 12 2)
        have b31884 := hb (x 14 13)
        have b31885 := hb (x 13 1 && x 13 14)
        clear * - r31882 b31883 b31884 b31885 d31865 d31625
        omega
      have d31886 : (x 13 1).toNat = 1 := by
        have r31887 := hand1 (x 13 1) (x 13 14)
        have b31888 := hb (x 13 1)
        have b31889 := hb (x 13 1 && x 13 14)
        clear * - r31887 b31888 b31889 d31881
        omega
      have d31890 : (x 14 14).toNat = 0 := by
        have r31891 : (x 14 14).toNat + (x 13 1).toNat = 1 := by have q := hd14 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31892 := hb (x 13 1)
        have b31893 := hb (x 14 14)
        clear * - r31891 b31892 b31893 d31886
        omega
      have d31894 : (x 14 1 && x 14 14).toNat = 0 := by
        have r31895 := hand2 (x 14 1) (x 14 14)
        have b31896 := hb (x 14 14)
        have b31897 := hb (x 14 1 && x 14 14)
        clear * - r31895 b31896 b31897 d31890
        omega
      have d31898 : (x 14 2).toNat = 0 := by
        have r31899 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
        have b31900 := hb (x 14 2)
        have b31901 := hb (x 14 14)
        clear * - r31899 b31900 b31901 d31890
        omega
      have d31902 : (x 13 2).toNat = 0 := by
        have r31903 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31904 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e31905 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b31906 := hb (x 12 3)
        have b31907 := hb (x 13 2)
        have b31908 := hb (x 14 13)
        have b31909 := hb (x 15 12)
        clear * - r31903 e31904 e31905 b31906 b31907 b31908 b31909 d31849 d31865 d31845
        omega
      have d31910 : (x 15 13).toNat = 1 := by
        have r31911 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31912 := hb (x 13 2)
        have b31913 := hb (x 15 13)
        have b31914 := hb (x 14 1 && x 14 14)
        clear * - r31911 b31912 b31913 b31914 d31894 d31902
        omega
      have d31915 : (x 16 12).toNat = 0 := by
        have r31916 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31917 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e31918 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b31919 := hb (x 13 3)
        have b31920 := hb (x 14 2)
        have b31921 := hb (x 15 13)
        have b31922 := hb (x 16 12)
        clear * - r31916 e31917 e31918 b31919 b31920 b31921 b31922 d31910 d31898
        omega
      have d31923 : (x 13 3).toNat = 0 := by
        have r31924 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31925 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e31926 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b31927 := hb (x 13 3)
        have b31928 := hb (x 14 2)
        have b31929 := hb (x 15 13)
        have b31930 := hb (x 16 12)
        clear * - r31924 e31925 e31926 b31927 b31928 b31929 b31930 d31915 d31910 d31898
        omega
      have d31931 : (x 13 3 && x 13 14).toNat = 0 := by
        have r31932 := hand1 (x 13 3) (x 13 14)
        have b31933 := hb (x 13 3)
        have b31934 := hb (x 13 3 && x 13 14)
        clear * - r31932 b31933 b31934 d31923
        omega
      have d31935 : (x 16 11).toNat = 1 := by
        have r31936 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31937 := hb (x 12 4)
        have b31938 := hb (x 16 11)
        have b31939 := hb (x 15 1 && x 15 12)
        have b31940 := hb (x 14 2 && x 14 13)
        have b31941 := hb (x 13 3 && x 13 14)
        clear * - r31936 b31937 b31938 b31939 b31940 b31941 d31857 d31873 d31931 d31822
        omega
      have d31942 : (x 16 3).toNat = 1 := by
        have r31943 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
        have b31944 := hb (x 16 3)
        have b31945 := hb (x 16 11)
        clear * - r31943 b31944 b31945 d31935
        omega
      have d31946 : (x 19 12).toNat = 0 := by
        have r31947 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31948 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e31949 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b31950 := hb (x 16 3)
        have b31951 := hb (x 17 2)
        have b31952 := hb (x 18 13)
        have b31953 := hb (x 19 12)
        clear * - r31947 e31948 e31949 b31950 b31951 b31952 b31953 d31942
        omega
      have d31954 : (x 18 13).toNat = 0 := by
        have r31955 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31956 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e31957 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b31958 := hb (x 16 3)
        have b31959 := hb (x 17 2)
        have b31960 := hb (x 18 13)
        have b31961 := hb (x 19 12)
        clear * - r31955 e31956 e31957 b31958 b31959 b31960 b31961 d31946 d31942
        omega
      have d31962 : (x 17 1 && x 17 14).toNat = 1 := by
        have r31963 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := by have q := hcov13 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31964 := hb (x 16 2)
        have b31965 := hb (x 18 13)
        have b31966 := hb (x 17 1 && x 17 14)
        clear * - r31963 b31964 b31965 b31966 d31954 d31806
        omega
      have d31967 : (x 17 14).toNat = 1 := by
        have r31968 := hand2 (x 17 1) (x 17 14)
        have b31969 := hb (x 17 14)
        have b31970 := hb (x 17 1 && x 17 14)
        clear * - r31968 b31969 b31970 d31962
        omega
      have d31971 : (x 16 1).toNat = 0 := by
        have r31972 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b31973 := hb (x 16 1)
        have b31974 := hb (x 17 14)
        clear * - r31972 b31973 b31974 d31967
        omega
      have d31975 : (x 16 1 && x 16 11).toNat = 0 := by
        have r31976 := hand1 (x 16 1) (x 16 11)
        have b31977 := hb (x 16 1)
        have b31978 := hb (x 16 1 && x 16 11)
        clear * - r31976 b31977 b31978 d31971
        omega
      have d31979 : (x 17 2).toNat = 0 := by
        have r31980 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e31981 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e31982 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b31983 := hb (x 16 3)
        have b31984 := hb (x 17 2)
        have b31985 := hb (x 18 13)
        have b31986 := hb (x 19 12)
        clear * - r31980 e31981 e31982 b31983 b31984 b31985 b31986 d31946 d31954 d31942
        omega
      have d31987 : (x 17 10).toNat = 0 := by
        have r31988 : (x 17 10).toNat ≤ (x 17 2).toNat := himp _ _ (hp10 17)
        have b31989 := hb (x 17 2)
        have b31990 := hb (x 17 10)
        clear * - r31988 b31989 b31990 d31979
        omega
      have r31991 : 1 ≤ (x 17 10).toNat + (x 16 1 && x 16 11).toNat + (x 15 2 && x 15 12).toNat + (x 14 3 && x 14 13).toNat + (x 13 4 && x 13 14).toNat + (x 12 5).toNat := by have q := hcov10 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b31992 := hb (x 12 5)
      have b31993 := hb (x 17 10)
      have b31994 := hb (x 16 1 && x 16 11)
      have b31995 := hb (x 15 2 && x 15 12)
      have b31996 := hb (x 14 3 && x 14 13)
      have b31997 := hb (x 13 4 && x 13 14)
      linarith only [r31991, b31992, b31993, b31994, b31995, b31996, b31997, d31987, d31975, d31861, d31877, d31759, d31771]

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1100 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x 0 12).toNat = 0)
    (g2 : (x 1 1).toNat = 1)
    (g3 : (x 1 2).toNat = 0)
    (g4 : (x 1 6).toNat = 0)
    (g5 : (x 1 10).toNat = 0)
    (g6 : (x 1 11).toNat = 0)
    (g7 : (x 1 14).toNat = 0)
    (g8 : (x 2 2).toNat = 0)
    (g9 : (x 2 10).toNat = 0)
    (g10 : (x 4 2).toNat = 0)
    (g11 : (x 4 4).toNat = 0)
    (g12 : (x 4 6).toNat = 0)
    (g13 : (x 4 10).toNat = 0)
    (g14 : (x 1 1 && x 1 3).toNat = 0)
    (g15 : (x 0 2 && x 0 4).toNat = 0)
    (g16 : (x 4 7 && x 4 10).toNat = 0)
    (g17 : (x 1 10 && x 1 13).toNat = 0)
    (g18 : (x 4 6 && x 4 10).toNat = 0)
    (g19 : (x 1 1 && x 1 6).toNat = 0)
    (g20 : (x 2 1 && x 2 10).toNat = 0)
    (g21 : (x 1 2 && x 1 11).toNat = 0)
    (g22 : (x 1 1 && x 1 11).toNat = 0)
    (g23 : (x 1 2 && x 1 12).toNat = 0)
    (g24 : (x 2 2 && x 2 12).toNat = 0)
    (g25 : (x 1 3 && x 1 13).toNat = 0)
    (g26 : (x 0 4 && x 0 14).toNat = 0)
    (g27 : (x 2 2 && x 2 13).toNat = 0)
    (g28 : (x 1 3 && x 1 14).toNat = 0)
    (g29 : (x 4 3 && x 4 14).toNat = 0)
    (g30 : (x 1 1 && x 1 14).toNat = 0)
    (g31 : (x 4 1 && x 4 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt1100_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31
