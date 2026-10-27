import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b10

Topic: combinatorics   Node: 724b7b6d44dd

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core: under the layer-free tight-cover constraints for k = 15 and 43 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b10_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 6).toNat = 0)
    (g1 : (x (-2) 11).toNat = 0)
    (g2 : (x (-1) 5).toNat = 0)
    (g3 : (x (-1) 9).toNat = 0)
    (g4 : (x (-1) 13).toNat = 0)
    (g5 : (x 0 4).toNat = 0)
    (g6 : (x 0 10).toNat = 0)
    (g7 : (x 0 11).toNat = 1)
    (g8 : (x 1 2).toNat = 0)
    (g9 : (x 1 5).toNat = 0)
    (g10 : (x 1 6).toNat = 0)
    (g11 : (x 1 10).toNat = 0)
    (g12 : (x 2 4).toNat = 0)
    (g13 : (x 2 5).toNat = 0)
    (g14 : (x 2 9).toNat = 0)
    (g15 : (x 3 4).toNat = 0)
    (g16 : (x 3 8).toNat = 0)
    (g17 : (x 4 9).toNat = 0)
    (g18 : (x 0 10 && x 0 12).toNat = 0)
    (g19 : (x (-1) 11 && x (-1) 13).toNat = 0)
    (g20 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g21 : (x 3 3 && x 3 8).toNat = 0)
    (g22 : (x 2 4 && x 2 9).toNat = 0)
    (g23 : (x 1 5 && x 1 10).toNat = 0)
    (g24 : (x 2 4 && x 2 10).toNat = 0)
    (g25 : (x 1 5 && x 1 11).toNat = 0)
    (g26 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g27 : (x 1 2 && x 1 11).toNat = 0)
    (g28 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g29 : (x (-2) 5 && x (-2) 14).toNat = 0)
    (g30 : (x 3 1 && x 3 10).toNat = 0)
    (g31 : (x 2 2 && x 2 11).toNat = 0)
    (g32 : (x 1 3 && x 1 12).toNat = 0)
    (g33 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g34 : (x 3 3 && x 3 12).toNat = 0)
    (g35 : (x 2 4 && x 2 13).toNat = 0)
    (g36 : (x 1 5 && x 1 14).toNat = 0)
    (g37 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g38 : (x 2 2 && x 2 12).toNat = 0)
    (g39 : (x 1 3 && x 1 13).toNat = 0)
    (g40 : (x 3 1 && x 3 12).toNat = 0)
    (g41 : (x 2 2 && x 2 13).toNat = 0)
    (g42 : (x 1 3 && x 1 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d17200 : (x 0 4 && x 0 14).toNat = 0 := by
    have r17201 := hand1 (x 0 4) (x 0 14)
    have b17202 := hb (x 0 4)
    have b17203 := hb (x 0 4 && x 0 14)
    clear * - r17201 b17202 b17203 g5
    omega
  have d17204 : (x 0 4 && x 0 13).toNat = 0 := by
    have r17205 := hand1 (x 0 4) (x 0 13)
    have b17206 := hb (x 0 4)
    have b17207 := hb (x 0 4 && x 0 13)
    clear * - r17205 b17206 b17207 g5
    omega
  have d17208 : (x 4 11).toNat = 1 := by
    have r17209 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17210 := hb (x 0 4)
    have b17211 := hb (x 4 11)
    have b17212 := hb (x 3 1 && x 3 12)
    have b17213 := hb (x 2 2 && x 2 13)
    have b17214 := hb (x 1 3 && x 1 14)
    clear * - r17209 b17210 b17211 b17212 b17213 b17214 g40 g41 g42 g5
    omega
  have d17215 : (x 4 3).toNat = 1 := by
    have r17216 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have b17217 := hb (x 4 3)
    have b17218 := hb (x 4 11)
    clear * - r17216 b17217 b17218 d17208
    omega
  have d17219 : (x 7 12).toNat = 0 := by
    have r17220 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17221 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e17222 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b17223 := hb (x 4 3)
    have b17224 := hb (x 5 2)
    have b17225 := hb (x 6 13)
    have b17226 := hb (x 7 12)
    clear * - r17220 e17221 e17222 b17223 b17224 b17225 b17226 d17215
    omega
  have d17227 : (x 7 1 && x 7 12).toNat = 0 := by
    have r17228 := hand2 (x 7 1) (x 7 12)
    have b17229 := hb (x 7 12)
    have b17230 := hb (x 7 1 && x 7 12)
    clear * - r17228 b17229 b17230 d17219
    omega
  have d17231 : (x 7 2 && x 7 12).toNat = 0 := by
    have r17232 := hand2 (x 7 2) (x 7 12)
    have b17233 := hb (x 7 12)
    have b17234 := hb (x 7 2 && x 7 12)
    clear * - r17232 b17233 b17234 d17219
    omega
  have d17235 : (x 7 4).toNat = 0 := by
    have r17236 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b17237 := hb (x 7 4)
    have b17238 := hb (x 7 12)
    clear * - r17236 b17237 b17238 d17219
    omega
  have d17239 : (x 7 4 && x 7 13).toNat = 0 := by
    have r17240 := hand1 (x 7 4) (x 7 13)
    have b17241 := hb (x 7 4)
    have b17242 := hb (x 7 4 && x 7 13)
    clear * - r17240 b17241 b17242 d17235
    omega
  have d17243 : (x 6 13).toNat = 0 := by
    have r17244 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17245 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e17246 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b17247 := hb (x 4 3)
    have b17248 := hb (x 5 2)
    have b17249 := hb (x 6 13)
    have b17250 := hb (x 7 12)
    clear * - r17244 e17245 e17246 b17247 b17248 b17249 b17250 d17219 d17215
    omega
  have d17251 : (x 6 2 && x 6 13).toNat = 0 := by
    have r17252 := hand2 (x 6 2) (x 6 13)
    have b17253 := hb (x 6 13)
    have b17254 := hb (x 6 2 && x 6 13)
    clear * - r17252 b17253 b17254 d17243
    omega
  have d17255 : (x 6 3 && x 6 13).toNat = 0 := by
    have r17256 := hand2 (x 6 3) (x 6 13)
    have b17257 := hb (x 6 13)
    have b17258 := hb (x 6 3 && x 6 13)
    clear * - r17256 b17257 b17258 d17243
    omega
  have d17259 : (x 6 5).toNat = 0 := by
    have r17260 : (x 6 5).toNat ≤ (x 6 13).toNat := himp _ _ (hp5 6)
    have b17261 := hb (x 6 5)
    have b17262 := hb (x 6 13)
    clear * - r17260 b17261 b17262 d17243
    omega
  have d17263 : (x 6 5 && x 6 14).toNat = 0 := by
    have r17264 := hand1 (x 6 5) (x 6 14)
    have b17265 := hb (x 6 5)
    have b17266 := hb (x 6 5 && x 6 14)
    clear * - r17264 b17265 b17266 d17259
    omega
  have d17267 : (x 5 2).toNat = 0 := by
    have r17268 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17269 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e17270 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b17271 := hb (x 4 3)
    have b17272 := hb (x 5 2)
    have b17273 := hb (x 6 13)
    have b17274 := hb (x 7 12)
    clear * - r17268 e17269 e17270 b17271 b17272 b17273 b17274 d17219 d17243 d17215
    omega
  have d17275 : (x 5 2 && x 5 13).toNat = 0 := by
    have r17276 := hand1 (x 5 2) (x 5 13)
    have b17277 := hb (x 5 2)
    have b17278 := hb (x 5 2 && x 5 13)
    clear * - r17276 b17277 b17278 d17267
    omega
  have d17279 : (x 5 10).toNat = 0 := by
    have r17280 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
    have b17281 := hb (x 5 2)
    have b17282 := hb (x 5 10)
    clear * - r17280 b17281 b17282 d17267
    omega
  have d17283 : (x 5 1 && x 5 10).toNat = 0 := by
    have r17284 := hand2 (x 5 1) (x 5 10)
    have b17285 := hb (x 5 10)
    have b17286 := hb (x 5 1 && x 5 10)
    clear * - r17284 b17285 b17286 d17279
    omega
  have d17287 : (x (-2) 6).toNat = 1 := by
    have r17288 : 1 ≤ (x 4 9).toNat + (x 3 1 && x 3 10).toNat + (x 2 2 && x 2 11).toNat + (x 1 3 && x 1 12).toNat + (x 0 4 && x 0 13).toNat + (x (-1) 5 && x (-1) 14).toNat + (x (-2) 6).toNat := by have q := hcov9 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17289 := hb (x (-2) 6)
    have b17290 := hb (x 4 9)
    have b17291 := hb (x 3 1 && x 3 10)
    have b17292 := hb (x 2 2 && x 2 11)
    have b17293 := hb (x 1 3 && x 1 12)
    have b17294 := hb (x 0 4 && x 0 13)
    have b17295 := hb (x (-1) 5 && x (-1) 14)
    clear * - r17288 b17289 b17290 b17291 b17292 b17293 b17294 b17295 g17 g30 g31 g32 d17204 g33
    omega
  have d17296 : (x (-2) 14).toNat = 1 := by
    have r17297 : (x (-2) 6).toNat ≤ (x (-2) 14).toNat := himp _ _ (hp6 (-2))
    have b17298 := hb (x (-2) 6)
    have b17299 := hb (x (-2) 14)
    clear * - r17297 b17298 b17299 d17287
    omega
  have d17300 : (x (-3) 1).toNat = 0 := by
    have r17301 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17302 := hb (x (-3) 1)
    have b17303 := hb (x (-2) 14)
    clear * - r17301 b17302 b17303 d17296
    omega
  have d17304 : (x (-3) 1 && x (-3) 12).toNat = 0 := by
    have r17305 := hand1 (x (-3) 1) (x (-3) 12)
    have b17306 := hb (x (-3) 1)
    have b17307 := hb (x (-3) 1 && x (-3) 12)
    clear * - r17305 b17306 b17307 d17300
    omega
  have d17308 : (x (-3) 13).toNat = 0 := by
    have r17309 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
    have b17310 := hb (x (-3) 1)
    have b17311 := hb (x (-3) 13)
    clear * - r17309 b17310 b17311 d17300
    omega
  have d17312 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
    have r17313 := hand2 (x (-3) 3) (x (-3) 13)
    have b17314 := hb (x (-3) 13)
    have b17315 := hb (x (-3) 3 && x (-3) 13)
    clear * - r17313 b17314 b17315 d17308
    omega
  have d17316 : (x (-3) 9).toNat = 0 := by
    have r17317 : (x (-3) 9).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp9 (-3))
    have b17318 := hb (x (-3) 1)
    have b17319 := hb (x (-3) 9)
    clear * - r17317 b17318 b17319 d17300
    omega
  have d17320 : (x (-3) 9 && x (-3) 14).toNat = 0 := by
    have r17321 := hand1 (x (-3) 9) (x (-3) 14)
    have b17322 := hb (x (-3) 9)
    have b17323 := hb (x (-3) 9 && x (-3) 14)
    clear * - r17321 b17322 b17323 d17316
    omega
  have d17324 : (x 7 8).toNat = 0 := by
    have r17325 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17326 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e17327 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e17328 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e17329 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e17330 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e17331 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b17332 := hb (x 0 7)
    have b17333 := hb (x 1 6)
    have b17334 := hb (x 2 5)
    have b17335 := hb (x 3 4)
    have b17336 := hb (x 4 11)
    have b17337 := hb (x 5 10)
    have b17338 := hb (x 6 9)
    have b17339 := hb (x 7 8)
    clear * - r17325 e17326 e17327 e17328 e17329 e17330 e17331 b17332 b17333 b17334 b17335 b17336 b17337 b17338 b17339 d17279 d17208 g15 g13 g10
    omega
  have d17340 : (x 6 9).toNat = 0 := by
    have r17341 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17342 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e17343 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e17344 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e17345 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e17346 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e17347 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b17348 := hb (x 0 7)
    have b17349 := hb (x 1 6)
    have b17350 := hb (x 2 5)
    have b17351 := hb (x 3 4)
    have b17352 := hb (x 4 11)
    have b17353 := hb (x 5 10)
    have b17354 := hb (x 6 9)
    have b17355 := hb (x 7 8)
    clear * - r17341 e17342 e17343 e17344 e17345 e17346 e17347 b17348 b17349 b17350 b17351 b17352 b17353 b17354 b17355 d17324 d17279 d17208 g15 g13 g10
    omega
  have d17356 : (x 4 8).toNat = 0 := by
    have r17357 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17358 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e17359 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e17360 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e17361 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e17362 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e17363 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b17364 := hb (x (-3) 7)
    have b17365 := hb (x (-2) 6)
    have b17366 := hb (x (-1) 5)
    have b17367 := hb (x 0 4)
    have b17368 := hb (x 1 11)
    have b17369 := hb (x 2 10)
    have b17370 := hb (x 3 9)
    have b17371 := hb (x 4 8)
    clear * - r17357 e17358 e17359 e17360 e17361 e17362 e17363 b17364 b17365 b17366 b17367 b17368 b17369 b17370 b17371 g5 g2 d17287
    omega
  have d17372 : (x 4 2 && x 4 8).toNat = 0 := by
    have r17373 := hand2 (x 4 2) (x 4 8)
    have b17374 := hb (x 4 8)
    have b17375 := hb (x 4 2 && x 4 8)
    clear * - r17373 b17374 b17375 d17356
    omega
  have d17376 : (x 4 4 && x 4 8).toNat = 0 := by
    have r17377 := hand2 (x 4 4) (x 4 8)
    have b17378 := hb (x 4 8)
    have b17379 := hb (x 4 4 && x 4 8)
    clear * - r17377 b17378 b17379 d17356
    omega
  have d17380 : (x 4 6 && x 4 8).toNat = 0 := by
    have r17381 := hand2 (x 4 6) (x 4 8)
    have b17382 := hb (x 4 8)
    have b17383 := hb (x 4 6 && x 4 8)
    clear * - r17381 b17382 b17383 d17356
    omega
  have d17384 : (x 3 9).toNat = 0 := by
    have r17385 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17386 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e17387 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e17388 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e17389 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e17390 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e17391 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b17392 := hb (x (-3) 7)
    have b17393 := hb (x (-2) 6)
    have b17394 := hb (x (-1) 5)
    have b17395 := hb (x 0 4)
    have b17396 := hb (x 1 11)
    have b17397 := hb (x 2 10)
    have b17398 := hb (x 3 9)
    have b17399 := hb (x 4 8)
    clear * - r17385 e17386 e17387 e17388 e17389 e17390 e17391 b17392 b17393 b17394 b17395 b17396 b17397 b17398 b17399 d17356 g5 g2 d17287
    omega
  have d17400 : (x 3 3 && x 3 9).toNat = 0 := by
    have r17401 := hand2 (x 3 3) (x 3 9)
    have b17402 := hb (x 3 9)
    have b17403 := hb (x 3 3 && x 3 9)
    clear * - r17401 b17402 b17403 d17384
    omega
  have d17404 : (x 3 5 && x 3 9).toNat = 0 := by
    have r17405 := hand2 (x 3 5) (x 3 9)
    have b17406 := hb (x 3 9)
    have b17407 := hb (x 3 5 && x 3 9)
    clear * - r17405 b17406 b17407 d17384
    omega
  have d17408 : (x 3 7 && x 3 9).toNat = 0 := by
    have r17409 := hand2 (x 3 7) (x 3 9)
    have b17410 := hb (x 3 9)
    have b17411 := hb (x 3 7 && x 3 9)
    clear * - r17409 b17410 b17411 d17384
    omega
  have d17412 : (x 2 10).toNat = 0 := by
    have r17413 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17414 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e17415 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e17416 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e17417 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e17418 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e17419 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b17420 := hb (x (-3) 7)
    have b17421 := hb (x (-2) 6)
    have b17422 := hb (x (-1) 5)
    have b17423 := hb (x 0 4)
    have b17424 := hb (x 1 11)
    have b17425 := hb (x 2 10)
    have b17426 := hb (x 3 9)
    have b17427 := hb (x 4 8)
    clear * - r17413 e17414 e17415 e17416 e17417 e17418 e17419 b17420 b17421 b17422 b17423 b17424 b17425 b17426 b17427 d17356 d17384 g5 g2 d17287
    omega
  have d17428 : (x 2 1 && x 2 10).toNat = 0 := by
    have r17429 := hand2 (x 2 1) (x 2 10)
    have b17430 := hb (x 2 10)
    have b17431 := hb (x 2 1 && x 2 10)
    clear * - r17429 b17430 b17431 d17412
    omega
  have d17432 : (x 0 3 && x 0 12).toNat = 1 := by
    have r17433 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b17434 := hb (x (-3) 6)
    have b17435 := hb (x 3 9)
    have b17436 := hb (x 2 1 && x 2 10)
    have b17437 := hb (x 1 2 && x 1 11)
    have b17438 := hb (x 0 3 && x 0 12)
    have b17439 := hb (x (-1) 4 && x (-1) 13)
    have b17440 := hb (x (-2) 5 && x (-2) 14)
    clear * - r17433 b17434 b17435 b17436 b17437 b17438 b17439 b17440 d17384 d17428 g27 g28 g29 g0
    omega
  have d17441 : (x 0 12).toNat = 1 := by
    have r17442 := hand2 (x 0 3) (x 0 12)
    have b17443 := hb (x 0 12)
    have b17444 := hb (x 0 3 && x 0 12)
    clear * - r17442 b17443 b17444 d17432
    omega
  have d17445 : (x (-2) 2).toNat = 0 := by
    have r17446 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17447 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e17448 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b17449 := hb (x (-3) 3)
    have b17450 := hb (x (-2) 2)
    have b17451 := hb (x (-1) 13)
    have b17452 := hb (x 0 12)
    clear * - r17446 e17447 e17448 b17449 b17450 b17451 b17452 d17441 g4
    omega
  have d17453 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
    have r17454 := hand1 (x (-2) 2) (x (-2) 12)
    have b17455 := hb (x (-2) 2)
    have b17456 := hb (x (-2) 2 && x (-2) 12)
    clear * - r17454 b17455 b17456 d17445
    omega
  have d17457 : (x (-2) 10).toNat = 0 := by
    have r17458 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
    have b17459 := hb (x (-2) 2)
    have b17460 := hb (x (-2) 10)
    clear * - r17458 b17459 b17460 d17445
    omega
  have d17461 : (x (-3) 3).toNat = 0 := by
    have r17462 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17463 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e17464 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b17465 := hb (x (-3) 3)
    have b17466 := hb (x (-2) 2)
    have b17467 := hb (x (-1) 13)
    have b17468 := hb (x 0 12)
    clear * - r17462 e17463 e17464 b17465 b17466 b17467 b17468 d17441 g4 d17445
    omega
  have d17469 : (x (-3) 11).toNat = 0 := by
    have r17470 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b17471 := hb (x (-3) 3)
    have b17472 := hb (x (-3) 11)
    clear * - r17470 b17471 b17472 d17461
    omega
  have d17473 : (x 2 6 && x 2 10).toNat = 0 := by
    have r17474 := hand2 (x 2 6) (x 2 10)
    have b17475 := hb (x 2 10)
    have b17476 := hb (x 2 6 && x 2 10)
    clear * - r17474 b17475 b17476 d17412
    omega
  have d17477 : (x 2 8 && x 2 10).toNat = 0 := by
    have r17478 := hand2 (x 2 8) (x 2 10)
    have b17479 := hb (x 2 10)
    have b17480 := hb (x 2 8 && x 2 10)
    clear * - r17478 b17479 b17480 d17412
    omega
  have d17481 : (x 1 11).toNat = 0 := by
    have r17482 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17483 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e17484 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e17485 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e17486 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e17487 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e17488 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b17489 := hb (x (-3) 7)
    have b17490 := hb (x (-2) 6)
    have b17491 := hb (x (-1) 5)
    have b17492 := hb (x 0 4)
    have b17493 := hb (x 1 11)
    have b17494 := hb (x 2 10)
    have b17495 := hb (x 3 9)
    have b17496 := hb (x 4 8)
    clear * - r17482 e17483 e17484 e17485 e17486 e17487 e17488 b17489 b17490 b17491 b17492 b17493 b17494 b17495 b17496 d17356 d17384 d17412 g5 g2 d17287
    omega
  have d17497 : (x 1 7 && x 1 11).toNat = 0 := by
    have r17498 := hand2 (x 1 7) (x 1 11)
    have b17499 := hb (x 1 11)
    have b17500 := hb (x 1 7 && x 1 11)
    clear * - r17498 b17499 b17500 d17481
    omega
  have d17501 : (x 1 9 && x 1 11).toNat = 0 := by
    have r17502 := hand2 (x 1 9) (x 1 11)
    have b17503 := hb (x 1 11)
    have b17504 := hb (x 1 9 && x 1 11)
    clear * - r17502 b17503 b17504 d17481
    omega
  cases h17505 : x 0 6
  · have f17506 : (x 0 6).toNat = 0 := by rw [h17505]; rfl
    have d17507 : (x 0 6 && x 0 12).toNat = 0 := by
      have r17508 := hand1 (x 0 6) (x 0 12)
      have b17509 := hb (x 0 6)
      have b17510 := hb (x 0 6 && x 0 12)
      clear * - r17508 b17509 b17510 f17506
      omega
    have d17511 : (x 0 6 && x 0 11).toNat = 0 := by
      have r17512 := hand1 (x 0 6) (x 0 11)
      have b17513 := hb (x 0 6)
      have b17514 := hb (x 0 6 && x 0 11)
      clear * - r17512 b17513 b17514 f17506
      omega
    have d17515 : (x 4 2 && x 4 11).toNat = 1 := by
      have r17516 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17517 := hb (x 0 6)
      have b17518 := hb (x 6 9)
      have b17519 := hb (x 5 1 && x 5 10)
      have b17520 := hb (x 4 2 && x 4 11)
      have b17521 := hb (x 3 3 && x 3 12)
      have b17522 := hb (x 2 4 && x 2 13)
      have b17523 := hb (x 1 5 && x 1 14)
      clear * - r17516 b17517 b17518 b17519 b17520 b17521 b17522 b17523 d17340 d17283 g34 g35 g36 f17506
      omega
    have d17524 : (x 4 2).toNat = 1 := by
      have r17525 := hand1 (x 4 2) (x 4 11)
      have b17526 := hb (x 4 2)
      have b17527 := hb (x 4 2 && x 4 11)
      clear * - r17525 b17526 b17527 d17515
      omega
    have d17528 : (x 4 14).toNat = 1 := by
      have r17529 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
      have b17530 := hb (x 4 2)
      have b17531 := hb (x 4 14)
      clear * - r17529 b17530 b17531 d17524
      omega
    have d17532 : (x 3 1).toNat = 0 := by
      have r17533 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17534 := hb (x 3 1)
      have b17535 := hb (x 4 14)
      clear * - r17533 b17534 b17535 d17528
      omega
    have d17536 : (x 3 1 && x 3 11).toNat = 0 := by
      have r17537 := hand1 (x 3 1) (x 3 11)
      have b17538 := hb (x 3 1)
      have b17539 := hb (x 3 1 && x 3 11)
      clear * - r17537 b17538 b17539 d17532
      omega
    have d17540 : (x 4 10).toNat = 1 := by
      have r17541 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17542 := hb (x (-1) 5)
      have b17543 := hb (x 4 10)
      have b17544 := hb (x 3 1 && x 3 11)
      have b17545 := hb (x 2 2 && x 2 12)
      have b17546 := hb (x 1 3 && x 1 13)
      have b17547 := hb (x 0 4 && x 0 14)
      clear * - r17541 b17542 b17543 b17544 b17545 b17546 b17547 d17536 g38 g39 d17200 g2
      omega
    have d17548 : (x 3 13).toNat = 0 := by
      have r17549 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b17550 := hb (x 3 1)
      have b17551 := hb (x 3 13)
      clear * - r17549 b17550 b17551 d17532
      omega
    have d17552 : (x 2 1 && x 2 14).toNat = 1 := by
      have r17553 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17554 := hb (x 1 2)
      have b17555 := hb (x 3 13)
      have b17556 := hb (x 2 1 && x 2 14)
      clear * - r17553 b17554 b17555 b17556 d17548 g8
      omega
    have d17557 : (x 2 1).toNat = 1 := by
      have r17558 := hand1 (x 2 1) (x 2 14)
      have b17559 := hb (x 2 1)
      have b17560 := hb (x 2 1 && x 2 14)
      clear * - r17558 b17559 b17560 d17552
      omega
    have d17561 : (x 3 14).toNat = 0 := by
      have r17562 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17563 := hb (x 2 1)
      have b17564 := hb (x 3 14)
      clear * - r17562 b17563 b17564 d17557
      omega
    have d17565 : (x 3 2).toNat = 0 := by
      have r17566 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b17567 := hb (x 3 2)
      have b17568 := hb (x 3 14)
      clear * - r17566 b17567 b17568 d17561
      omega
    have d17569 : (x 6 12).toNat = 0 := by
      have r17570 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17571 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e17572 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b17573 := hb (x 3 3)
      have b17574 := hb (x 4 2)
      have b17575 := hb (x 5 13)
      have b17576 := hb (x 6 12)
      clear * - r17570 e17571 e17572 b17573 b17574 b17575 b17576 d17524
      omega
    have d17577 : (x 6 4).toNat = 0 := by
      have r17578 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
      have b17579 := hb (x 6 4)
      have b17580 := hb (x 6 12)
      clear * - r17578 b17579 b17580 d17569
      omega
    have d17581 : (x 6 4 && x 6 6).toNat = 0 := by
      have r17582 := hand1 (x 6 4) (x 6 6)
      have b17583 := hb (x 6 4)
      have b17584 := hb (x 6 4 && x 6 6)
      clear * - r17582 b17583 b17584 d17577
      omega
    have d17585 : (x 5 13).toNat = 0 := by
      have r17586 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17587 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e17588 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b17589 := hb (x 3 3)
      have b17590 := hb (x 4 2)
      have b17591 := hb (x 5 13)
      have b17592 := hb (x 6 12)
      clear * - r17586 e17587 e17588 b17589 b17590 b17591 b17592 d17569 d17524
      omega
    have d17593 : (x 5 5).toNat = 0 := by
      have r17594 : (x 5 5).toNat ≤ (x 5 13).toNat := himp _ _ (hp5 5)
      have b17595 := hb (x 5 5)
      have b17596 := hb (x 5 13)
      clear * - r17594 b17595 b17596 d17585
      omega
    have d17597 : (x 5 5 && x 5 7).toNat = 0 := by
      have r17598 := hand1 (x 5 5) (x 5 7)
      have b17599 := hb (x 5 5)
      have b17600 := hb (x 5 5 && x 5 7)
      clear * - r17598 b17599 b17600 d17593
      omega
    have d17601 : (x 4 1 && x 4 14).toNat = 1 := by
      have r17602 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17603 := hb (x 3 2)
      have b17604 := hb (x 5 13)
      have b17605 := hb (x 4 1 && x 4 14)
      clear * - r17602 b17603 b17604 b17605 d17585 d17565
      omega
    have d17606 : (x 4 1).toNat = 1 := by
      have r17607 := hand1 (x 4 1) (x 4 14)
      have b17608 := hb (x 4 1)
      have b17609 := hb (x 4 1 && x 4 14)
      clear * - r17607 b17608 b17609 d17601
      omega
    have d17610 : (x 5 14).toNat = 0 := by
      have r17611 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17612 := hb (x 4 1)
      have b17613 := hb (x 5 14)
      clear * - r17611 b17612 b17613 d17606
      omega
    have d17614 : (x 5 6).toNat = 0 := by
      have r17615 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
      have b17616 := hb (x 5 6)
      have b17617 := hb (x 5 14)
      clear * - r17615 b17616 b17617 d17610
      omega
    have d17618 : (x 5 1 && x 5 6).toNat = 0 := by
      have r17619 := hand2 (x 5 1) (x 5 6)
      have b17620 := hb (x 5 6)
      have b17621 := hb (x 5 1 && x 5 6)
      clear * - r17619 b17620 b17621 d17614
      omega
    have d17622 : (x 3 3).toNat = 0 := by
      have r17623 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17624 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e17625 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b17626 := hb (x 3 3)
      have b17627 := hb (x 4 2)
      have b17628 := hb (x 5 13)
      have b17629 := hb (x 6 12)
      clear * - r17623 e17624 e17625 b17626 b17627 b17628 b17629 d17569 d17585 d17524
      omega
    have d17630 : (x 3 11).toNat = 0 := by
      have r17631 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b17632 := hb (x 3 3)
      have b17633 := hb (x 3 11)
      clear * - r17631 b17632 b17633 d17622
      omega
    have d17634 : (x 6 8).toNat = 0 := by
      have r17635 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17636 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e17637 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e17638 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e17639 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e17640 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e17641 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b17642 := hb (x (-1) 7)
      have b17643 := hb (x 0 6)
      have b17644 := hb (x 1 5)
      have b17645 := hb (x 2 4)
      have b17646 := hb (x 3 11)
      have b17647 := hb (x 4 10)
      have b17648 := hb (x 5 9)
      have b17649 := hb (x 6 8)
      clear * - r17635 e17636 e17637 e17638 e17639 e17640 e17641 b17642 b17643 b17644 b17645 b17646 b17647 b17648 b17649 d17540 d17630 g12 g9 f17506
      omega
    have d17650 : (x 5 9).toNat = 0 := by
      have r17651 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17652 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e17653 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e17654 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e17655 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e17656 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e17657 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b17658 := hb (x (-1) 7)
      have b17659 := hb (x 0 6)
      have b17660 := hb (x 1 5)
      have b17661 := hb (x 2 4)
      have b17662 := hb (x 3 11)
      have b17663 := hb (x 4 10)
      have b17664 := hb (x 5 9)
      have b17665 := hb (x 6 8)
      clear * - r17651 e17652 e17653 e17654 e17655 e17656 e17657 b17658 b17659 b17660 b17661 b17662 b17663 b17664 b17665 d17634 d17540 d17630 g12 g9 f17506
      omega
    have d17666 : (x (-1) 7).toNat = 0 := by
      have r17667 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17668 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e17669 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e17670 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e17671 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e17672 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e17673 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b17674 := hb (x (-1) 7)
      have b17675 := hb (x 0 6)
      have b17676 := hb (x 1 5)
      have b17677 := hb (x 2 4)
      have b17678 := hb (x 3 11)
      have b17679 := hb (x 4 10)
      have b17680 := hb (x 5 9)
      have b17681 := hb (x 6 8)
      clear * - r17667 e17668 e17669 e17670 e17671 e17672 e17673 b17674 b17675 b17676 b17677 b17678 b17679 b17680 b17681 d17634 d17650 d17540 d17630 g12 g9 f17506
      omega
    have d17682 : (x (-1) 7 && x (-1) 12).toNat = 0 := by
      have r17683 := hand1 (x (-1) 7) (x (-1) 12)
      have b17684 := hb (x (-1) 7)
      have b17685 := hb (x (-1) 7 && x (-1) 12)
      clear * - r17683 b17684 b17685 d17666
      omega
    have r17686 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r17687 : (x 11 1).toNat + (x 10 2).toNat + (x 9 3).toNat + (x 8 4).toNat + (x 7 5).toNat + (x 6 6).toNat + (x 5 7).toNat + (x 4 8).toNat + (x 3 9).toNat + (x 2 10).toNat + (x 1 11).toNat + (x 0 12).toNat + (x (-1) 13).toNat + (x (-2) 14).toNat = 3 := by have q := hcount 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r17688 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17689 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
    have e17690 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
    have e17691 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
    have e17692 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
    have e17693 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
    have e17694 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
    have r17695 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := by have q := hd8 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17696 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
    have e17697 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
    have e17698 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
    have e17699 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
    have e17700 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
    have e17701 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
    have r17702 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17703 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
    have e17704 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
    have e17705 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
    have e17706 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
    have e17707 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
    have e17708 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
    have r17709 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17710 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
    have e17711 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
    have r17712 : 1 ≤ (x 10 2).toNat + (x 9 1 && x 9 3).toNat + (x 8 2 && x 8 4).toNat + (x 7 3 && x 7 5).toNat + (x 6 4 && x 6 6).toNat + (x 5 5 && x 5 7).toNat + (x 4 6 && x 4 8).toNat + (x 3 7 && x 3 9).toNat + (x 2 8 && x 2 10).toNat + (x 1 9 && x 1 11).toNat + (x 0 10 && x 0 12).toNat + (x (-1) 11 && x (-1) 13).toNat + (x (-2) 12 && x (-2) 14).toNat + (x (-3) 13).toNat := by have q := hcov2 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r17713 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e17714 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
    have e17715 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
    have r17716 : 1 ≤ (x 6 5).toNat + (x 5 1 && x 5 6).toNat + (x 4 2 && x 4 7).toNat + (x 3 3 && x 3 8).toNat + (x 2 4 && x 2 9).toNat + (x 1 5 && x 1 10).toNat + (x 0 6 && x 0 11).toNat + (x (-1) 7 && x (-1) 12).toNat + (x (-2) 8 && x (-2) 13).toNat + (x (-3) 9 && x (-3) 14).toNat + (x (-4) 10).toNat := by have q := hcov5 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r17717 : 1 ≤ (x 6 6).toNat + (x 5 1 && x 5 7).toNat + (x 4 2 && x 4 8).toNat + (x 3 3 && x 3 9).toNat + (x 2 4 && x 2 10).toNat + (x 1 5 && x 1 11).toNat + (x 0 6 && x 0 12).toNat + (x (-1) 7 && x (-1) 13).toNat + (x (-2) 8 && x (-2) 14).toNat + (x (-3) 9).toNat := by have q := hcov6 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r17718 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r17719 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := by have q := hcov10 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r17720 : 1 ≤ (x (-2) 11).toNat + (x (-3) 1 && x (-3) 12).toNat + (x (-4) 2 && x (-4) 13).toNat + (x (-5) 3 && x (-5) 14).toNat + (x (-6) 4).toNat := by have q := hcov11 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r17721 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r17722 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
    have r17723 := hand2 (x 9 1) (x 9 3)
    have r17724 := hand2 (x 8 2) (x 8 4)
    have r17725 := hand2 (x 7 3) (x 7 5)
    have r17726 := hand1 (x (-2) 12) (x (-2) 14)
    have r17727 := hand2 (x 6 2) (x 6 6)
    have r17728 := hand2 (x 5 3) (x 5 7)
    have r17729 := hand1 (x 0 8) (x 0 12)
    have r17730 := hand2 (x 4 2) (x 4 7)
    have r17731 := hand2 (x (-2) 8) (x (-2) 13)
    have r17732 := hand2 (x 5 1) (x 5 7)
    have r17733 := hand1 (x (-2) 8) (x (-2) 14)
    have r17734 := hand2 (x 10 1) (x 10 10)
    have r17735 := hand2 (x 9 2) (x 9 11)
    have r17736 := hand1 (x 8 3) (x 8 12)
    have r17737 := hand1 (x (-4) 4) (x (-4) 14)
    have r17738 := hand1 (x (-4) 2) (x (-4) 13)
    have r17739 := hand1 (x (-5) 3) (x (-5) 14)
    have r17740 := hand1 (x 10 1) (x 10 14)
    linarith only [r17686, r17687, r17688, e17689, e17690, e17691, e17692, e17693, e17694, r17695, e17696, e17697, e17698, e17699, e17700, e17701, r17702, e17703, e17704, e17705, e17706, e17707, e17708, r17709, e17710, e17711, r17712, r17713, e17714, e17715, r17716, r17717, r17718, r17719, r17720, r17721, r17722, r17723, r17724, r17725, r17726, r17727, r17728, r17729, r17730, r17731, r17732, r17733, r17734, r17735, r17736, r17737, r17738, r17739, r17740, d17316, d17469, d17308, d17457, g1, d17296, g3, g4, g6, g7, d17441, g11, d17481, g14, d17412, g16, d17384, d17356, d17614, d17259, d17235, d17581, d17597, d17380, d17408, d17477, d17501, g18, g19, d17376, d17404, d17473, d17497, g20, d17618, g21, g22, g23, d17511, d17682, d17320, d17372, d17400, g24, g25, d17507, g26, d17239, d17263, g37, d17453, d17312, d17304]
  · have f17846 : (x 0 6).toNat = 1 := by rw [h17505]; rfl
    have d17847 : (x 6 8).toNat = 0 := by
      have r17848 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17849 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e17850 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e17851 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e17852 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e17853 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e17854 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b17855 := hb (x (-1) 7)
      have b17856 := hb (x 0 6)
      have b17857 := hb (x 1 5)
      have b17858 := hb (x 2 4)
      have b17859 := hb (x 3 11)
      have b17860 := hb (x 4 10)
      have b17861 := hb (x 5 9)
      have b17862 := hb (x 6 8)
      clear * - r17848 e17849 e17850 e17851 e17852 e17853 e17854 b17855 b17856 b17857 b17858 b17859 b17860 b17861 b17862 g12 g9 f17846
      omega
    have d17863 : (x 5 9).toNat = 0 := by
      have r17864 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17865 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e17866 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e17867 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e17868 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e17869 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e17870 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b17871 := hb (x (-1) 7)
      have b17872 := hb (x 0 6)
      have b17873 := hb (x 1 5)
      have b17874 := hb (x 2 4)
      have b17875 := hb (x 3 11)
      have b17876 := hb (x 4 10)
      have b17877 := hb (x 5 9)
      have b17878 := hb (x 6 8)
      clear * - r17864 e17865 e17866 e17867 e17868 e17869 e17870 b17871 b17872 b17873 b17874 b17875 b17876 b17877 b17878 d17847 g12 g9 f17846
      omega
    have d17879 : (x 4 10).toNat = 0 := by
      have r17880 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17881 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
      have e17882 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
      have e17883 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
      have e17884 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
      have e17885 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
      have e17886 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
      have b17887 := hb (x (-1) 7)
      have b17888 := hb (x 0 6)
      have b17889 := hb (x 1 5)
      have b17890 := hb (x 2 4)
      have b17891 := hb (x 3 11)
      have b17892 := hb (x 4 10)
      have b17893 := hb (x 5 9)
      have b17894 := hb (x 6 8)
      clear * - r17880 e17881 e17882 e17883 e17884 e17885 e17886 b17887 b17888 b17889 b17890 b17891 b17892 b17893 b17894 d17847 d17863 g12 g9 f17846
      omega
    have d17895 : (x 3 1 && x 3 11).toNat = 1 := by
      have r17896 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17897 := hb (x (-1) 5)
      have b17898 := hb (x 4 10)
      have b17899 := hb (x 3 1 && x 3 11)
      have b17900 := hb (x 2 2 && x 2 12)
      have b17901 := hb (x 1 3 && x 1 13)
      have b17902 := hb (x 0 4 && x 0 14)
      clear * - r17896 b17897 b17898 b17899 b17900 b17901 b17902 d17879 g38 g39 d17200 g2
      omega
    have d17903 : (x 3 11).toNat = 1 := by
      have r17904 := hand2 (x 3 1) (x 3 11)
      have b17905 := hb (x 3 11)
      have b17906 := hb (x 3 1 && x 3 11)
      clear * - r17904 b17905 b17906 d17895
      omega
    have d17907 : (x 3 3).toNat = 1 := by
      have r17908 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b17909 := hb (x 3 3)
      have b17910 := hb (x 3 11)
      clear * - r17908 b17909 b17910 d17903
      omega
    have d17911 : (x 6 12).toNat = 0 := by
      have r17912 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17913 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e17914 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b17915 := hb (x 3 3)
      have b17916 := hb (x 4 2)
      have b17917 := hb (x 5 13)
      have b17918 := hb (x 6 12)
      clear * - r17912 e17913 e17914 b17915 b17916 b17917 b17918 d17907
      omega
    have d17919 : (x 6 1 && x 6 12).toNat = 0 := by
      have r17920 := hand2 (x 6 1) (x 6 12)
      have b17921 := hb (x 6 12)
      have b17922 := hb (x 6 1 && x 6 12)
      clear * - r17920 b17921 b17922 d17911
      omega
    have d17923 : (x 5 13).toNat = 0 := by
      have r17924 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17925 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e17926 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b17927 := hb (x 3 3)
      have b17928 := hb (x 4 2)
      have b17929 := hb (x 5 13)
      have b17930 := hb (x 6 12)
      clear * - r17924 e17925 e17926 b17927 b17928 b17929 b17930 d17911 d17907
      omega
    have d17931 : (x 4 2).toNat = 0 := by
      have r17932 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e17933 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e17934 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b17935 := hb (x 3 3)
      have b17936 := hb (x 4 2)
      have b17937 := hb (x 5 13)
      have b17938 := hb (x 6 12)
      clear * - r17932 e17933 e17934 b17935 b17936 b17937 b17938 d17911 d17923 d17907
      omega
    have d17939 : (x 5 1 && x 5 14).toNat = 1 := by
      have r17940 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17941 := hb (x 4 2)
      have b17942 := hb (x 6 13)
      have b17943 := hb (x 5 1 && x 5 14)
      clear * - r17940 b17941 b17942 b17943 d17243 d17931
      omega
    have d17944 : (x 5 14).toNat = 1 := by
      have r17945 := hand2 (x 5 1) (x 5 14)
      have b17946 := hb (x 5 14)
      have b17947 := hb (x 5 1 && x 5 14)
      clear * - r17945 b17946 b17947 d17939
      omega
    have d17948 : (x 4 1).toNat = 0 := by
      have r17949 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17950 := hb (x 4 1)
      have b17951 := hb (x 5 14)
      clear * - r17949 b17950 b17951 d17944
      omega
    have d17952 : (x 4 1 && x 4 14).toNat = 0 := by
      have r17953 := hand1 (x 4 1) (x 4 14)
      have b17954 := hb (x 4 1)
      have b17955 := hb (x 4 1 && x 4 14)
      clear * - r17953 b17954 b17955 d17948
      omega
    have d17956 : (x 3 2).toNat = 1 := by
      have r17957 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17958 := hb (x 3 2)
      have b17959 := hb (x 5 13)
      have b17960 := hb (x 4 1 && x 4 14)
      clear * - r17957 b17958 b17959 b17960 d17923 d17952
      omega
    have d17961 : (x 3 14).toNat = 1 := by
      have r17962 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
      have b17963 := hb (x 3 2)
      have b17964 := hb (x 3 14)
      clear * - r17962 b17963 b17964 d17956
      omega
    have d17965 : (x 2 1).toNat = 0 := by
      have r17966 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17967 := hb (x 2 1)
      have b17968 := hb (x 3 14)
      clear * - r17966 b17967 b17968 d17961
      omega
    have d17969 : (x 2 1 && x 2 14).toNat = 0 := by
      have r17970 := hand1 (x 2 1) (x 2 14)
      have b17971 := hb (x 2 1)
      have b17972 := hb (x 2 1 && x 2 14)
      clear * - r17970 b17971 b17972 d17965
      omega
    have d17973 : (x 3 13).toNat = 1 := by
      have r17974 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := by have q := hcov13 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17975 := hb (x 1 2)
      have b17976 := hb (x 3 13)
      have b17977 := hb (x 2 1 && x 2 14)
      clear * - r17974 b17975 b17976 b17977 d17969 g8
      omega
    have d17978 : (x 3 1).toNat = 1 := by
      have r17979 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b17980 := hb (x 3 1)
      have b17981 := hb (x 3 13)
      clear * - r17979 b17980 b17981 d17973
      omega
    have d17982 : (x 4 14).toNat = 0 := by
      have r17983 : (x 4 14).toNat + (x 3 1).toNat = 1 := by have q := hd14 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17984 := hb (x 3 1)
      have b17985 := hb (x 4 14)
      clear * - r17983 b17984 b17985 d17978
      omega
    have d17986 : (x 4 3 && x 4 14).toNat = 0 := by
      have r17987 := hand2 (x 4 3) (x 4 14)
      have b17988 := hb (x 4 14)
      have b17989 := hb (x 4 3 && x 4 14)
      clear * - r17987 b17988 b17989 d17982
      omega
    have d17990 : (x 7 11).toNat = 1 := by
      have r17991 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b17992 := hb (x 3 4)
      have b17993 := hb (x 7 11)
      have b17994 := hb (x 6 1 && x 6 12)
      have b17995 := hb (x 5 2 && x 5 13)
      have b17996 := hb (x 4 3 && x 4 14)
      clear * - r17991 b17992 b17993 b17994 b17995 b17996 d17919 d17275 d17986 g15
      omega
    have d17997 : (x 7 3).toNat = 1 := by
      have r17998 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
      have b17999 := hb (x 7 3)
      have b18000 := hb (x 7 11)
      clear * - r17998 b17999 b18000 d17990
      omega
    have d18001 : (x 10 12).toNat = 0 := by
      have r18002 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18003 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e18004 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b18005 := hb (x 7 3)
      have b18006 := hb (x 8 2)
      have b18007 := hb (x 9 13)
      have b18008 := hb (x 10 12)
      clear * - r18002 e18003 e18004 b18005 b18006 b18007 b18008 d17997
      omega
    have d18009 : (x 9 13).toNat = 0 := by
      have r18010 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18011 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e18012 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b18013 := hb (x 7 3)
      have b18014 := hb (x 8 2)
      have b18015 := hb (x 9 13)
      have b18016 := hb (x 10 12)
      clear * - r18010 e18011 e18012 b18013 b18014 b18015 b18016 d18001 d17997
      omega
    have d18017 : (x 8 2).toNat = 0 := by
      have r18018 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18019 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e18020 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b18021 := hb (x 7 3)
      have b18022 := hb (x 8 2)
      have b18023 := hb (x 9 13)
      have b18024 := hb (x 10 12)
      clear * - r18018 e18019 e18020 b18021 b18022 b18023 b18024 d18001 d18009 d17997
      omega
    have d18025 : (x 4 12).toNat = 0 := by
      have r18026 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18027 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e18028 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b18029 := hb (x 1 3)
      have b18030 := hb (x 2 2)
      have b18031 := hb (x 3 13)
      have b18032 := hb (x 4 12)
      clear * - r18026 e18027 e18028 b18029 b18030 b18031 b18032 d17973
      omega
    have d18033 : (x 4 4).toNat = 0 := by
      have r18034 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
      have b18035 := hb (x 4 4)
      have b18036 := hb (x 4 12)
      clear * - r18034 b18035 b18036 d18025
      omega
    have d18037 : (x 5 12).toNat = 0 := by
      have r18038 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18039 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e18040 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b18041 := hb (x 2 3)
      have b18042 := hb (x 3 2)
      have b18043 := hb (x 4 13)
      have b18044 := hb (x 5 12)
      clear * - r18038 e18039 e18040 b18041 b18042 b18043 b18044 d17956
      omega
    have d18045 : (x 5 4).toNat = 0 := by
      have r18046 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
      have b18047 := hb (x 5 4)
      have b18048 := hb (x 5 12)
      clear * - r18046 b18047 b18048 d18037
      omega
    have d18049 : (x 5 4 && x 5 14).toNat = 0 := by
      have r18050 := hand1 (x 5 4) (x 5 14)
      have b18051 := hb (x 5 4)
      have b18052 := hb (x 5 4 && x 5 14)
      clear * - r18050 b18051 b18052 d18045
      omega
    have d18053 : (x 4 13).toNat = 0 := by
      have r18054 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18055 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
      have e18056 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
      have b18057 := hb (x 2 3)
      have b18058 := hb (x 3 2)
      have b18059 := hb (x 4 13)
      have b18060 := hb (x 5 12)
      clear * - r18054 e18055 e18056 b18057 b18058 b18059 b18060 d18037 d17956
      omega
    have d18061 : (x 4 5).toNat = 0 := by
      have r18062 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
      have b18063 := hb (x 4 5)
      have b18064 := hb (x 4 13)
      clear * - r18062 b18063 b18064 d18053
      omega
    have d18065 : (x 5 1).toNat = 1 := by
      have r18066 := hand1 (x 5 1) (x 5 14)
      have b18067 := hb (x 5 1)
      have b18068 := hb (x 5 1 && x 5 14)
      clear * - r18066 b18067 b18068 d17939
      omega
    have d18069 : (x 6 14).toNat = 0 := by
      have r18070 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18071 := hb (x 5 1)
      have b18072 := hb (x 6 14)
      clear * - r18070 b18071 b18072 d18065
      omega
    have d18073 : (x 6 1 && x 6 14).toNat = 0 := by
      have r18074 := hand2 (x 6 1) (x 6 14)
      have b18075 := hb (x 6 14)
      have b18076 := hb (x 6 1 && x 6 14)
      clear * - r18074 b18075 b18076 d18069
      omega
    have d18077 : (x 7 13).toNat = 1 := by
      have r18078 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18079 := hb (x 5 2)
      have b18080 := hb (x 7 13)
      have b18081 := hb (x 6 1 && x 6 14)
      clear * - r18078 b18079 b18080 b18081 d18073 d17267
      omega
    have d18082 : (x 8 12).toNat = 0 := by
      have r18083 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18084 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e18085 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b18086 := hb (x 5 3)
      have b18087 := hb (x 6 2)
      have b18088 := hb (x 7 13)
      have b18089 := hb (x 8 12)
      clear * - r18083 e18084 e18085 b18086 b18087 b18088 b18089 d18077
      omega
    have d18090 : (x 6 2).toNat = 0 := by
      have r18091 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18092 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e18093 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b18094 := hb (x 5 3)
      have b18095 := hb (x 6 2)
      have b18096 := hb (x 7 13)
      have b18097 := hb (x 8 12)
      clear * - r18091 e18092 e18093 b18094 b18095 b18096 b18097 d18082 d18077
      omega
    have d18098 : (x 5 3).toNat = 0 := by
      have r18099 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18100 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e18101 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b18102 := hb (x 5 3)
      have b18103 := hb (x 6 2)
      have b18104 := hb (x 7 13)
      have b18105 := hb (x 8 12)
      clear * - r18099 e18100 e18101 b18102 b18103 b18104 b18105 d18082 d18077 d18090
      omega
    have d18106 : (x 5 3 && x 5 14).toNat = 0 := by
      have r18107 := hand1 (x 5 3) (x 5 14)
      have b18108 := hb (x 5 3)
      have b18109 := hb (x 5 3 && x 5 14)
      clear * - r18107 b18108 b18109 d18098
      omega
    have d18110 : (x 8 11).toNat = 1 := by
      have r18111 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18112 := hb (x 4 4)
      have b18113 := hb (x 8 11)
      have b18114 := hb (x 7 1 && x 7 12)
      have b18115 := hb (x 6 2 && x 6 13)
      have b18116 := hb (x 5 3 && x 5 14)
      clear * - r18111 b18112 b18113 b18114 b18115 b18116 d17227 d17251 d18106 d18033
      omega
    have d18117 : (x 8 3).toNat = 1 := by
      have r18118 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
      have b18119 := hb (x 8 3)
      have b18120 := hb (x 8 11)
      clear * - r18118 b18119 b18120 d18110
      omega
    have d18121 : (x 11 12).toNat = 0 := by
      have r18122 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18123 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e18124 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b18125 := hb (x 8 3)
      have b18126 := hb (x 9 2)
      have b18127 := hb (x 10 13)
      have b18128 := hb (x 11 12)
      clear * - r18122 e18123 e18124 b18125 b18126 b18127 b18128 d18117
      omega
    have d18129 : (x 10 13).toNat = 0 := by
      have r18130 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18131 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e18132 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b18133 := hb (x 8 3)
      have b18134 := hb (x 9 2)
      have b18135 := hb (x 10 13)
      have b18136 := hb (x 11 12)
      clear * - r18130 e18131 e18132 b18133 b18134 b18135 b18136 d18121 d18117
      omega
    have d18137 : (x 9 1 && x 9 14).toNat = 1 := by
      have r18138 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18139 := hb (x 8 2)
      have b18140 := hb (x 10 13)
      have b18141 := hb (x 9 1 && x 9 14)
      clear * - r18138 b18139 b18140 b18141 d18129 d18017
      omega
    have d18142 : (x 9 14).toNat = 1 := by
      have r18143 := hand2 (x 9 1) (x 9 14)
      have b18144 := hb (x 9 14)
      have b18145 := hb (x 9 1 && x 9 14)
      clear * - r18143 b18144 b18145 d18137
      omega
    have d18146 : (x 8 1).toNat = 0 := by
      have r18147 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18148 := hb (x 8 1)
      have b18149 := hb (x 9 14)
      clear * - r18147 b18148 b18149 d18142
      omega
    have d18150 : (x 8 1 && x 8 11).toNat = 0 := by
      have r18151 := hand1 (x 8 1) (x 8 11)
      have b18152 := hb (x 8 1)
      have b18153 := hb (x 8 1 && x 8 11)
      clear * - r18151 b18152 b18153 d18146
      omega
    have d18154 : (x 9 10).toNat = 1 := by
      have r18155 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18156 := hb (x 4 5)
      have b18157 := hb (x 9 10)
      have b18158 := hb (x 8 1 && x 8 11)
      have b18159 := hb (x 7 2 && x 7 12)
      have b18160 := hb (x 6 3 && x 6 13)
      have b18161 := hb (x 5 4 && x 5 14)
      clear * - r18155 b18156 b18157 b18158 b18159 b18160 b18161 d18150 d17231 d17255 d18049 d18061
      omega
    have d18162 : (x 9 2).toNat = 1 := by
      have r18163 : (x 9 10).toNat ≤ (x 9 2).toNat := himp _ _ (hp10 9)
      have b18164 := hb (x 9 2)
      have b18165 := hb (x 9 10)
      clear * - r18163 b18164 b18165 d18154
      omega
    have r18166 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18167 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e18168 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b18169 := hb (x 8 3)
    have b18170 := hb (x 9 2)
    have b18171 := hb (x 10 13)
    have b18172 := hb (x 11 12)
    linarith only [r18166, e18167, e18168, b18169, b18170, b18171, b18172, d18121, d18129, d18162, d18117]

theorem cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b10 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-3) 6).toNat = 0)
    (g1 : (x (-2) 11).toNat = 0)
    (g2 : (x (-1) 5).toNat = 0)
    (g3 : (x (-1) 9).toNat = 0)
    (g4 : (x (-1) 13).toNat = 0)
    (g5 : (x 0 4).toNat = 0)
    (g6 : (x 0 10).toNat = 0)
    (g7 : (x 0 11).toNat = 1)
    (g8 : (x 1 2).toNat = 0)
    (g9 : (x 1 5).toNat = 0)
    (g10 : (x 1 6).toNat = 0)
    (g11 : (x 1 10).toNat = 0)
    (g12 : (x 2 4).toNat = 0)
    (g13 : (x 2 5).toNat = 0)
    (g14 : (x 2 9).toNat = 0)
    (g15 : (x 3 4).toNat = 0)
    (g16 : (x 3 8).toNat = 0)
    (g17 : (x 4 9).toNat = 0)
    (g18 : (x 0 10 && x 0 12).toNat = 0)
    (g19 : (x (-1) 11 && x (-1) 13).toNat = 0)
    (g20 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g21 : (x 3 3 && x 3 8).toNat = 0)
    (g22 : (x 2 4 && x 2 9).toNat = 0)
    (g23 : (x 1 5 && x 1 10).toNat = 0)
    (g24 : (x 2 4 && x 2 10).toNat = 0)
    (g25 : (x 1 5 && x 1 11).toNat = 0)
    (g26 : (x (-1) 7 && x (-1) 13).toNat = 0)
    (g27 : (x 1 2 && x 1 11).toNat = 0)
    (g28 : (x (-1) 4 && x (-1) 13).toNat = 0)
    (g29 : (x (-2) 5 && x (-2) 14).toNat = 0)
    (g30 : (x 3 1 && x 3 10).toNat = 0)
    (g31 : (x 2 2 && x 2 11).toNat = 0)
    (g32 : (x 1 3 && x 1 12).toNat = 0)
    (g33 : (x (-1) 5 && x (-1) 14).toNat = 0)
    (g34 : (x 3 3 && x 3 12).toNat = 0)
    (g35 : (x 2 4 && x 2 13).toNat = 0)
    (g36 : (x 1 5 && x 1 14).toNat = 0)
    (g37 : (x (-1) 1 && x (-1) 11).toNat = 0)
    (g38 : (x 2 2 && x 2 12).toNat = 0)
    (g39 : (x 1 3 && x 1 13).toNat = 0)
    (g40 : (x 3 1 && x 3 12).toNat = 0)
    (g41 : (x 2 2 && x 2 13).toNat = 0)
    (g42 : (x 1 3 && x 1 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_ten_iff_eleven_core_b10_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42
