import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0001

Topic: combinatorics   Node: 167cc5e88a80

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 3 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 2).toNat = 0)
    (g1 : (x 0 3).toNat = 1)
    (g2 : (x 0 4).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d14181 : (x 3 12).toNat = 0 := by
    have r14182 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
    have e14183 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e14184 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b14185 := hb (x 0 3)
    have b14186 := hb (x 1 2)
    have b14187 := hb (x 2 13)
    have b14188 := hb (x 3 12)
    clear * - r14182 e14183 e14184 b14185 b14186 b14187 b14188 g1
    omega
  have d14189 : (x 3 1 && x 3 12).toNat = 0 := by
    have r14190 := hand2 (x 3 1) (x 3 12)
    have b14191 := hb (x 3 12)
    have b14192 := hb (x 3 1 && x 3 12)
    clear * - r14190 b14191 b14192 d14181
    omega
  have d14193 : (x 3 4).toNat = 0 := by
    have r14194 : (x 3 4).toNat ≤ (x 3 12).toNat := himp _ _ (hp4 3)
    have b14195 := hb (x 3 4)
    have b14196 := hb (x 3 12)
    clear * - r14194 b14195 b14196 d14181
    omega
  have d14197 : (x 2 13).toNat = 0 := by
    have r14198 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
    have e14199 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e14200 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b14201 := hb (x 0 3)
    have b14202 := hb (x 1 2)
    have b14203 := hb (x 2 13)
    have b14204 := hb (x 3 12)
    clear * - r14198 e14199 e14200 b14201 b14202 b14203 b14204 d14181 g1
    omega
  have d14205 : (x 2 2 && x 2 13).toNat = 0 := by
    have r14206 := hand2 (x 2 2) (x 2 13)
    have b14207 := hb (x 2 13)
    have b14208 := hb (x 2 2 && x 2 13)
    clear * - r14206 b14207 b14208 d14197
    omega
  have d14209 : (x 1 1 && x 1 14).toNat = 1 := by
    have r14210 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := hcov13 2
    have b14211 := hb (x 0 2)
    have b14212 := hb (x 2 13)
    have b14213 := hb (x 1 1 && x 1 14)
    clear * - r14210 b14211 b14212 b14213 d14197 g0
    omega
  have d14214 : (x 1 1).toNat = 1 := by
    have r14215 := hand1 (x 1 1) (x 1 14)
    have b14216 := hb (x 1 1)
    have b14217 := hb (x 1 1 && x 1 14)
    clear * - r14215 b14216 b14217 d14209
    omega
  have d14218 : (x 2 14).toNat = 0 := by
    have r14219 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
    have b14220 := hb (x 1 1)
    have b14221 := hb (x 2 14)
    clear * - r14219 b14220 b14221 d14214
    omega
  have d14222 : (x 2 1 && x 2 14).toNat = 0 := by
    have r14223 := hand2 (x 2 1) (x 2 14)
    have b14224 := hb (x 2 14)
    have b14225 := hb (x 2 1 && x 2 14)
    clear * - r14223 b14224 b14225 d14218
    omega
  have d14226 : (x 2 2).toNat = 0 := by
    have r14227 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
    have b14228 := hb (x 2 2)
    have b14229 := hb (x 2 14)
    clear * - r14227 b14228 b14229 d14218
    omega
  have d14230 : (x 1 2).toNat = 0 := by
    have r14231 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := hd12 3
    have e14232 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
    have e14233 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
    have b14234 := hb (x 0 3)
    have b14235 := hb (x 1 2)
    have b14236 := hb (x 2 13)
    have b14237 := hb (x 3 12)
    clear * - r14231 e14232 e14233 b14234 b14235 b14236 b14237 d14181 d14197 g1
    omega
  have d14238 : (x 3 13).toNat = 1 := by
    have r14239 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
    have b14240 := hb (x 1 2)
    have b14241 := hb (x 3 13)
    have b14242 := hb (x 2 1 && x 2 14)
    clear * - r14239 b14240 b14241 b14242 d14222 d14230
    omega
  have d14243 : (x 3 1).toNat = 1 := by
    have r14244 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b14245 := hb (x 3 1)
    have b14246 := hb (x 3 13)
    clear * - r14244 b14245 b14246 d14238
    omega
  have d14247 : (x 4 14).toNat = 0 := by
    have r14248 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
    have b14249 := hb (x 3 1)
    have b14250 := hb (x 4 14)
    clear * - r14248 b14249 b14250 d14243
    omega
  have d14251 : (x 4 3 && x 4 14).toNat = 0 := by
    have r14252 := hand2 (x 4 3) (x 4 14)
    have b14253 := hb (x 4 14)
    have b14254 := hb (x 4 3 && x 4 14)
    clear * - r14252 b14253 b14254 d14247
    omega
  have d14255 : (x 4 2).toNat = 0 := by
    have r14256 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
    have b14257 := hb (x 4 2)
    have b14258 := hb (x 4 14)
    clear * - r14256 b14257 b14258 d14247
    omega
  have d14259 : (x 4 12).toNat = 0 := by
    have r14260 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
    have e14261 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e14262 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b14263 := hb (x 1 3)
    have b14264 := hb (x 2 2)
    have b14265 := hb (x 3 13)
    have b14266 := hb (x 4 12)
    clear * - r14260 e14261 e14262 b14263 b14264 b14265 b14266 d14238 d14226
    omega
  have d14267 : (x 4 4).toNat = 0 := by
    have r14268 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b14269 := hb (x 4 4)
    have b14270 := hb (x 4 12)
    clear * - r14268 b14269 b14270 d14259
    omega
  have d14271 : (x 1 3).toNat = 0 := by
    have r14272 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
    have e14273 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e14274 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b14275 := hb (x 1 3)
    have b14276 := hb (x 2 2)
    have b14277 := hb (x 3 13)
    have b14278 := hb (x 4 12)
    clear * - r14272 e14273 e14274 b14275 b14276 b14277 b14278 d14259 d14238 d14226
    omega
  have d14279 : (x 1 3 && x 1 14).toNat = 0 := by
    have r14280 := hand1 (x 1 3) (x 1 14)
    have b14281 := hb (x 1 3)
    have b14282 := hb (x 1 3 && x 1 14)
    clear * - r14280 b14281 b14282 d14271
    omega
  have d14283 : (x 4 11).toNat = 1 := by
    have r14284 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := hcov11 4
    have b14285 := hb (x 0 4)
    have b14286 := hb (x 4 11)
    have b14287 := hb (x 3 1 && x 3 12)
    have b14288 := hb (x 2 2 && x 2 13)
    have b14289 := hb (x 1 3 && x 1 14)
    clear * - r14284 b14285 b14286 b14287 b14288 b14289 d14189 d14205 d14279 g2
    omega
  have d14290 : (x 4 3).toNat = 1 := by
    have r14291 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have b14292 := hb (x 4 3)
    have b14293 := hb (x 4 11)
    clear * - r14291 b14292 b14293 d14283
    omega
  have d14294 : (x 7 12).toNat = 0 := by
    have r14295 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
    have e14296 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e14297 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b14298 := hb (x 4 3)
    have b14299 := hb (x 5 2)
    have b14300 := hb (x 6 13)
    have b14301 := hb (x 7 12)
    clear * - r14295 e14296 e14297 b14298 b14299 b14300 b14301 d14290
    omega
  have d14302 : (x 7 1 && x 7 12).toNat = 0 := by
    have r14303 := hand2 (x 7 1) (x 7 12)
    have b14304 := hb (x 7 12)
    have b14305 := hb (x 7 1 && x 7 12)
    clear * - r14303 b14304 b14305 d14294
    omega
  have d14306 : (x 7 4).toNat = 0 := by
    have r14307 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
    have b14308 := hb (x 7 4)
    have b14309 := hb (x 7 12)
    clear * - r14307 b14308 b14309 d14294
    omega
  have d14310 : (x 6 13).toNat = 0 := by
    have r14311 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
    have e14312 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e14313 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b14314 := hb (x 4 3)
    have b14315 := hb (x 5 2)
    have b14316 := hb (x 6 13)
    have b14317 := hb (x 7 12)
    clear * - r14311 e14312 e14313 b14314 b14315 b14316 b14317 d14294 d14290
    omega
  have d14318 : (x 6 2 && x 6 13).toNat = 0 := by
    have r14319 := hand2 (x 6 2) (x 6 13)
    have b14320 := hb (x 6 13)
    have b14321 := hb (x 6 2 && x 6 13)
    clear * - r14319 b14320 b14321 d14310
    omega
  have d14322 : (x 5 1 && x 5 14).toNat = 1 := by
    have r14323 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
    have b14324 := hb (x 4 2)
    have b14325 := hb (x 6 13)
    have b14326 := hb (x 5 1 && x 5 14)
    clear * - r14323 b14324 b14325 b14326 d14310 d14255
    omega
  have d14327 : (x 5 1).toNat = 1 := by
    have r14328 := hand1 (x 5 1) (x 5 14)
    have b14329 := hb (x 5 1)
    have b14330 := hb (x 5 1 && x 5 14)
    clear * - r14328 b14329 b14330 d14322
    omega
  have d14331 : (x 6 14).toNat = 0 := by
    have r14332 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
    have b14333 := hb (x 5 1)
    have b14334 := hb (x 6 14)
    clear * - r14332 b14333 b14334 d14327
    omega
  have d14335 : (x 6 1 && x 6 14).toNat = 0 := by
    have r14336 := hand2 (x 6 1) (x 6 14)
    have b14337 := hb (x 6 14)
    have b14338 := hb (x 6 1 && x 6 14)
    clear * - r14336 b14337 b14338 d14331
    omega
  have d14339 : (x 6 2).toNat = 0 := by
    have r14340 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
    have b14341 := hb (x 6 2)
    have b14342 := hb (x 6 14)
    clear * - r14340 b14341 b14342 d14331
    omega
  have d14343 : (x 5 2).toNat = 0 := by
    have r14344 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
    have e14345 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e14346 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have b14347 := hb (x 4 3)
    have b14348 := hb (x 5 2)
    have b14349 := hb (x 6 13)
    have b14350 := hb (x 7 12)
    clear * - r14344 e14345 e14346 b14347 b14348 b14349 b14350 d14294 d14310 d14290
    omega
  have d14351 : (x 5 2 && x 5 13).toNat = 0 := by
    have r14352 := hand1 (x 5 2) (x 5 13)
    have b14353 := hb (x 5 2)
    have b14354 := hb (x 5 2 && x 5 13)
    clear * - r14352 b14353 b14354 d14343
    omega
  have d14355 : (x 7 13).toNat = 1 := by
    have r14356 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
    have b14357 := hb (x 5 2)
    have b14358 := hb (x 7 13)
    have b14359 := hb (x 6 1 && x 6 14)
    clear * - r14356 b14357 b14358 b14359 d14335 d14343
    omega
  have d14360 : (x 7 1).toNat = 1 := by
    have r14361 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b14362 := hb (x 7 1)
    have b14363 := hb (x 7 13)
    clear * - r14361 b14362 b14363 d14355
    omega
  have d14364 : (x 8 14).toNat = 0 := by
    have r14365 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
    have b14366 := hb (x 7 1)
    have b14367 := hb (x 8 14)
    clear * - r14365 b14366 b14367 d14360
    omega
  have d14368 : (x 8 3 && x 8 14).toNat = 0 := by
    have r14369 := hand2 (x 8 3) (x 8 14)
    have b14370 := hb (x 8 14)
    have b14371 := hb (x 8 3 && x 8 14)
    clear * - r14369 b14370 b14371 d14364
    omega
  have d14372 : (x 8 2).toNat = 0 := by
    have r14373 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
    have b14374 := hb (x 8 2)
    have b14375 := hb (x 8 14)
    clear * - r14373 b14374 b14375 d14364
    omega
  have d14376 : (x 8 12).toNat = 0 := by
    have r14377 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
    have e14378 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e14379 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b14380 := hb (x 5 3)
    have b14381 := hb (x 6 2)
    have b14382 := hb (x 7 13)
    have b14383 := hb (x 8 12)
    clear * - r14377 e14378 e14379 b14380 b14381 b14382 b14383 d14355 d14339
    omega
  have d14384 : (x 8 4).toNat = 0 := by
    have r14385 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
    have b14386 := hb (x 8 4)
    have b14387 := hb (x 8 12)
    clear * - r14385 b14386 b14387 d14376
    omega
  have d14388 : (x 5 3).toNat = 0 := by
    have r14389 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
    have e14390 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
    have e14391 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
    have b14392 := hb (x 5 3)
    have b14393 := hb (x 6 2)
    have b14394 := hb (x 7 13)
    have b14395 := hb (x 8 12)
    clear * - r14389 e14390 e14391 b14392 b14393 b14394 b14395 d14376 d14355 d14339
    omega
  have d14396 : (x 5 3 && x 5 14).toNat = 0 := by
    have r14397 := hand1 (x 5 3) (x 5 14)
    have b14398 := hb (x 5 3)
    have b14399 := hb (x 5 3 && x 5 14)
    clear * - r14397 b14398 b14399 d14388
    omega
  have d14400 : (x 8 11).toNat = 1 := by
    have r14401 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := hcov11 8
    have b14402 := hb (x 4 4)
    have b14403 := hb (x 8 11)
    have b14404 := hb (x 7 1 && x 7 12)
    have b14405 := hb (x 6 2 && x 6 13)
    have b14406 := hb (x 5 3 && x 5 14)
    clear * - r14401 b14402 b14403 b14404 b14405 b14406 d14302 d14318 d14396 d14267
    omega
  have d14407 : (x 8 3).toNat = 1 := by
    have r14408 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
    have b14409 := hb (x 8 3)
    have b14410 := hb (x 8 11)
    clear * - r14408 b14409 b14410 d14400
    omega
  have d14411 : (x 11 12).toNat = 0 := by
    have r14412 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
    have e14413 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e14414 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b14415 := hb (x 8 3)
    have b14416 := hb (x 9 2)
    have b14417 := hb (x 10 13)
    have b14418 := hb (x 11 12)
    clear * - r14412 e14413 e14414 b14415 b14416 b14417 b14418 d14407
    omega
  have d14419 : (x 11 1 && x 11 12).toNat = 0 := by
    have r14420 := hand2 (x 11 1) (x 11 12)
    have b14421 := hb (x 11 12)
    have b14422 := hb (x 11 1 && x 11 12)
    clear * - r14420 b14421 b14422 d14411
    omega
  have d14423 : (x 11 4).toNat = 0 := by
    have r14424 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
    have b14425 := hb (x 11 4)
    have b14426 := hb (x 11 12)
    clear * - r14424 b14425 b14426 d14411
    omega
  have d14427 : (x 10 13).toNat = 0 := by
    have r14428 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
    have e14429 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e14430 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b14431 := hb (x 8 3)
    have b14432 := hb (x 9 2)
    have b14433 := hb (x 10 13)
    have b14434 := hb (x 11 12)
    clear * - r14428 e14429 e14430 b14431 b14432 b14433 b14434 d14411 d14407
    omega
  have d14435 : (x 10 2 && x 10 13).toNat = 0 := by
    have r14436 := hand2 (x 10 2) (x 10 13)
    have b14437 := hb (x 10 13)
    have b14438 := hb (x 10 2 && x 10 13)
    clear * - r14436 b14437 b14438 d14427
    omega
  have d14439 : (x 9 1 && x 9 14).toNat = 1 := by
    have r14440 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
    have b14441 := hb (x 8 2)
    have b14442 := hb (x 10 13)
    have b14443 := hb (x 9 1 && x 9 14)
    clear * - r14440 b14441 b14442 b14443 d14427 d14372
    omega
  have d14444 : (x 9 14).toNat = 1 := by
    have r14445 := hand2 (x 9 1) (x 9 14)
    have b14446 := hb (x 9 14)
    have b14447 := hb (x 9 1 && x 9 14)
    clear * - r14445 b14446 b14447 d14439
    omega
  have d14448 : (x 8 1).toNat = 0 := by
    have r14449 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
    have b14450 := hb (x 8 1)
    have b14451 := hb (x 9 14)
    clear * - r14449 b14450 b14451 d14444
    omega
  have d14452 : (x 8 13).toNat = 0 := by
    have r14453 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b14454 := hb (x 8 1)
    have b14455 := hb (x 8 13)
    clear * - r14453 b14454 b14455 d14448
    omega
  have d14456 : (x 7 1 && x 7 14).toNat = 1 := by
    have r14457 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
    have b14458 := hb (x 6 2)
    have b14459 := hb (x 8 13)
    have b14460 := hb (x 7 1 && x 7 14)
    clear * - r14457 b14458 b14459 b14460 d14452 d14339
    omega
  have d14461 : (x 7 14).toNat = 1 := by
    have r14462 := hand2 (x 7 1) (x 7 14)
    have b14463 := hb (x 7 14)
    have b14464 := hb (x 7 1 && x 7 14)
    clear * - r14462 b14463 b14464 d14456
    omega
  have d14465 : (x 6 1).toNat = 0 := by
    have r14466 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
    have b14467 := hb (x 6 1)
    have b14468 := hb (x 7 14)
    clear * - r14466 b14467 b14468 d14461
    omega
  have d14469 : (x 6 1 && x 6 12).toNat = 0 := by
    have r14470 := hand1 (x 6 1) (x 6 12)
    have b14471 := hb (x 6 1)
    have b14472 := hb (x 6 1 && x 6 12)
    clear * - r14470 b14471 b14472 d14465
    omega
  have d14473 : (x 7 11).toNat = 1 := by
    have r14474 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := hcov11 7
    have b14475 := hb (x 3 4)
    have b14476 := hb (x 7 11)
    have b14477 := hb (x 6 1 && x 6 12)
    have b14478 := hb (x 5 2 && x 5 13)
    have b14479 := hb (x 4 3 && x 4 14)
    clear * - r14474 b14475 b14476 b14477 b14478 b14479 d14469 d14351 d14251 d14193
    omega
  have d14480 : (x 7 3).toNat = 1 := by
    have r14481 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
    have b14482 := hb (x 7 3)
    have b14483 := hb (x 7 11)
    clear * - r14481 b14482 b14483 d14473
    omega
  have d14484 : (x 10 12).toNat = 0 := by
    have r14485 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
    have e14486 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e14487 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b14488 := hb (x 7 3)
    have b14489 := hb (x 8 2)
    have b14490 := hb (x 9 13)
    have b14491 := hb (x 10 12)
    clear * - r14485 e14486 e14487 b14488 b14489 b14490 b14491 d14372 d14480
    omega
  have d14492 : (x 10 1 && x 10 12).toNat = 0 := by
    have r14493 := hand2 (x 10 1) (x 10 12)
    have b14494 := hb (x 10 12)
    have b14495 := hb (x 10 1 && x 10 12)
    clear * - r14493 b14494 b14495 d14484
    omega
  have d14496 : (x 9 13).toNat = 0 := by
    have r14497 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
    have e14498 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
    have e14499 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
    have b14500 := hb (x 7 3)
    have b14501 := hb (x 8 2)
    have b14502 := hb (x 9 13)
    have b14503 := hb (x 10 12)
    clear * - r14497 e14498 e14499 b14500 b14501 b14502 b14503 d14484 d14372 d14480
    omega
  have d14504 : (x 9 2 && x 9 13).toNat = 0 := by
    have r14505 := hand2 (x 9 2) (x 9 13)
    have b14506 := hb (x 9 13)
    have b14507 := hb (x 9 2 && x 9 13)
    clear * - r14505 b14506 b14507 d14496
    omega
  have d14508 : (x 11 11).toNat = 1 := by
    have r14509 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := hcov11 11
    have b14510 := hb (x 7 4)
    have b14511 := hb (x 11 11)
    have b14512 := hb (x 10 1 && x 10 12)
    have b14513 := hb (x 9 2 && x 9 13)
    have b14514 := hb (x 8 3 && x 8 14)
    clear * - r14509 b14510 b14511 b14512 b14513 b14514 d14492 d14504 d14368 d14306
    omega
  have d14515 : (x 11 3).toNat = 1 := by
    have r14516 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
    have b14517 := hb (x 11 3)
    have b14518 := hb (x 11 11)
    clear * - r14516 b14517 b14518 d14508
    omega
  have d14519 : (x 14 12).toNat = 0 := by
    have r14520 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
    have e14521 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e14522 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b14523 := hb (x 11 3)
    have b14524 := hb (x 12 2)
    have b14525 := hb (x 13 13)
    have b14526 := hb (x 14 12)
    clear * - r14520 e14521 e14522 b14523 b14524 b14525 b14526 d14515
    omega
  have d14527 : (x 14 1 && x 14 12).toNat = 0 := by
    have r14528 := hand2 (x 14 1) (x 14 12)
    have b14529 := hb (x 14 12)
    have b14530 := hb (x 14 1 && x 14 12)
    clear * - r14528 b14529 b14530 d14519
    omega
  have d14531 : (x 13 13).toNat = 0 := by
    have r14532 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
    have e14533 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e14534 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b14535 := hb (x 11 3)
    have b14536 := hb (x 12 2)
    have b14537 := hb (x 13 13)
    have b14538 := hb (x 14 12)
    clear * - r14532 e14533 e14534 b14535 b14536 b14537 b14538 d14519 d14515
    omega
  have d14539 : (x 13 2 && x 13 13).toNat = 0 := by
    have r14540 := hand2 (x 13 2) (x 13 13)
    have b14541 := hb (x 13 13)
    have b14542 := hb (x 13 2 && x 13 13)
    clear * - r14540 b14541 b14542 d14531
    omega
  have d14543 : (x 12 2).toNat = 0 := by
    have r14544 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := hd12 14
    have e14545 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
    have e14546 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
    have b14547 := hb (x 11 3)
    have b14548 := hb (x 12 2)
    have b14549 := hb (x 13 13)
    have b14550 := hb (x 14 12)
    clear * - r14544 e14545 e14546 b14547 b14548 b14549 b14550 d14519 d14531 d14515
    omega
  have d14551 : (x 9 1).toNat = 1 := by
    have r14552 := hand1 (x 9 1) (x 9 14)
    have b14553 := hb (x 9 1)
    have b14554 := hb (x 9 1 && x 9 14)
    clear * - r14552 b14553 b14554 d14439
    omega
  have d14555 : (x 10 14).toNat = 0 := by
    have r14556 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
    have b14557 := hb (x 9 1)
    have b14558 := hb (x 10 14)
    clear * - r14556 b14557 b14558 d14551
    omega
  have d14559 : (x 10 1 && x 10 14).toNat = 0 := by
    have r14560 := hand2 (x 10 1) (x 10 14)
    have b14561 := hb (x 10 14)
    have b14562 := hb (x 10 1 && x 10 14)
    clear * - r14560 b14561 b14562 d14555
    omega
  have d14563 : (x 10 2).toNat = 0 := by
    have r14564 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
    have b14565 := hb (x 10 2)
    have b14566 := hb (x 10 14)
    clear * - r14564 b14565 b14566 d14555
    omega
  have d14567 : (x 9 2).toNat = 0 := by
    have r14568 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := hd12 11
    have e14569 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
    have e14570 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
    have b14571 := hb (x 8 3)
    have b14572 := hb (x 9 2)
    have b14573 := hb (x 10 13)
    have b14574 := hb (x 11 12)
    clear * - r14568 e14569 e14570 b14571 b14572 b14573 b14574 d14411 d14427 d14407
    omega
  have d14575 : (x 11 13).toNat = 1 := by
    have r14576 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
    have b14577 := hb (x 9 2)
    have b14578 := hb (x 11 13)
    have b14579 := hb (x 10 1 && x 10 14)
    clear * - r14576 b14577 b14578 b14579 d14559 d14567
    omega
  have d14580 : (x 11 1).toNat = 1 := by
    have r14581 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
    have b14582 := hb (x 11 1)
    have b14583 := hb (x 11 13)
    clear * - r14581 b14582 b14583 d14575
    omega
  have d14584 : (x 12 14).toNat = 0 := by
    have r14585 : (x 12 14).toNat + (x 11 1).toNat = 1 := hd14 12
    have b14586 := hb (x 11 1)
    have b14587 := hb (x 12 14)
    clear * - r14585 b14586 b14587 d14580
    omega
  have d14588 : (x 12 1 && x 12 14).toNat = 0 := by
    have r14589 := hand2 (x 12 1) (x 12 14)
    have b14590 := hb (x 12 14)
    have b14591 := hb (x 12 1 && x 12 14)
    clear * - r14589 b14590 b14591 d14584
    omega
  have d14592 : (x 11 2).toNat = 1 := by
    have r14593 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
    have b14594 := hb (x 11 2)
    have b14595 := hb (x 13 13)
    have b14596 := hb (x 12 1 && x 12 14)
    clear * - r14593 b14594 b14595 b14596 d14531 d14588
    omega
  have d14597 : (x 13 12).toNat = 0 := by
    have r14598 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e14599 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e14600 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b14601 := hb (x 10 3)
    have b14602 := hb (x 11 2)
    have b14603 := hb (x 12 13)
    have b14604 := hb (x 13 12)
    clear * - r14598 e14599 e14600 b14601 b14602 b14603 b14604 d14592
    omega
  have d14605 : (x 13 4).toNat = 0 := by
    have r14606 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
    have b14607 := hb (x 13 4)
    have b14608 := hb (x 13 12)
    clear * - r14606 b14607 b14608 d14597
    omega
  have d14609 : (x 13 4 && x 13 14).toNat = 0 := by
    have r14610 := hand1 (x 13 4) (x 13 14)
    have b14611 := hb (x 13 4)
    have b14612 := hb (x 13 4 && x 13 14)
    clear * - r14610 b14611 b14612 d14605
    omega
  have d14613 : (x 12 13).toNat = 0 := by
    have r14614 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e14615 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e14616 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b14617 := hb (x 10 3)
    have b14618 := hb (x 11 2)
    have b14619 := hb (x 12 13)
    have b14620 := hb (x 13 12)
    clear * - r14614 e14615 e14616 b14617 b14618 b14619 b14620 d14597 d14592
    omega
  have d14621 : (x 12 5).toNat = 0 := by
    have r14622 : (x 12 5).toNat ≤ (x 12 13).toNat := himp _ _ (hp5 12)
    have b14623 := hb (x 12 5)
    have b14624 := hb (x 12 13)
    clear * - r14622 b14623 b14624 d14613
    omega
  have d14625 : (x 12 3 && x 12 14).toNat = 0 := by
    have r14626 := hand2 (x 12 3) (x 12 14)
    have b14627 := hb (x 12 14)
    have b14628 := hb (x 12 3 && x 12 14)
    clear * - r14626 b14627 b14628 d14584
    omega
  have d14629 : (x 15 11).toNat = 1 := by
    have r14630 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := hcov11 15
    have b14631 := hb (x 11 4)
    have b14632 := hb (x 15 11)
    have b14633 := hb (x 14 1 && x 14 12)
    have b14634 := hb (x 13 2 && x 13 13)
    have b14635 := hb (x 12 3 && x 12 14)
    clear * - r14630 b14631 b14632 b14633 b14634 b14635 d14527 d14539 d14625 d14423
    omega
  have d14636 : (x 15 3).toNat = 1 := by
    have r14637 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
    have b14638 := hb (x 15 3)
    have b14639 := hb (x 15 11)
    clear * - r14637 b14638 b14639 d14629
    omega
  have d14640 : (x 18 12).toNat = 0 := by
    have r14641 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
    have e14642 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e14643 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b14644 := hb (x 15 3)
    have b14645 := hb (x 16 2)
    have b14646 := hb (x 17 13)
    have b14647 := hb (x 18 12)
    clear * - r14641 e14642 e14643 b14644 b14645 b14646 b14647 d14636
    omega
  have d14648 : (x 17 13).toNat = 0 := by
    have r14649 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
    have e14650 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e14651 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b14652 := hb (x 15 3)
    have b14653 := hb (x 16 2)
    have b14654 := hb (x 17 13)
    have b14655 := hb (x 18 12)
    clear * - r14649 e14650 e14651 b14652 b14653 b14654 b14655 d14640 d14636
    omega
  have d14656 : (x 16 2).toNat = 0 := by
    have r14657 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
    have e14658 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
    have e14659 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
    have b14660 := hb (x 15 3)
    have b14661 := hb (x 16 2)
    have b14662 := hb (x 17 13)
    have b14663 := hb (x 18 12)
    clear * - r14657 e14658 e14659 b14660 b14661 b14662 b14663 d14640 d14648 d14636
    omega
  have d14664 : (x 12 12).toNat = 0 := by
    have r14665 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
    have e14666 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e14667 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b14668 := hb (x 9 3)
    have b14669 := hb (x 10 2)
    have b14670 := hb (x 11 13)
    have b14671 := hb (x 12 12)
    clear * - r14665 e14666 e14667 b14668 b14669 b14670 b14671 d14575 d14563
    omega
  have d14672 : (x 12 4).toNat = 0 := by
    have r14673 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
    have b14674 := hb (x 12 4)
    have b14675 := hb (x 12 12)
    clear * - r14673 b14674 b14675 d14664
    omega
  have d14676 : (x 9 3).toNat = 0 := by
    have r14677 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
    have e14678 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
    have e14679 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
    have b14680 := hb (x 9 3)
    have b14681 := hb (x 10 2)
    have b14682 := hb (x 11 13)
    have b14683 := hb (x 12 12)
    clear * - r14677 e14678 e14679 b14680 b14681 b14682 b14683 d14664 d14575 d14563
    omega
  have d14684 : (x 9 3 && x 9 14).toNat = 0 := by
    have r14685 := hand1 (x 9 3) (x 9 14)
    have b14686 := hb (x 9 3)
    have b14687 := hb (x 9 3 && x 9 14)
    clear * - r14685 b14686 b14687 d14676
    omega
  have d14688 : (x 12 11).toNat = 1 := by
    have r14689 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := hcov11 12
    have b14690 := hb (x 8 4)
    have b14691 := hb (x 12 11)
    have b14692 := hb (x 11 1 && x 11 12)
    have b14693 := hb (x 10 2 && x 10 13)
    have b14694 := hb (x 9 3 && x 9 14)
    clear * - r14689 b14690 b14691 b14692 b14693 b14694 d14419 d14435 d14684 d14384
    omega
  have d14695 : (x 12 3).toNat = 1 := by
    have r14696 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
    have b14697 := hb (x 12 3)
    have b14698 := hb (x 12 11)
    clear * - r14696 b14697 b14698 d14688
    omega
  have d14699 : (x 15 12).toNat = 0 := by
    have r14700 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
    have e14701 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e14702 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b14703 := hb (x 12 3)
    have b14704 := hb (x 13 2)
    have b14705 := hb (x 14 13)
    have b14706 := hb (x 15 12)
    clear * - r14700 e14701 e14702 b14703 b14704 b14705 b14706 d14695
    omega
  have d14707 : (x 15 1 && x 15 12).toNat = 0 := by
    have r14708 := hand2 (x 15 1) (x 15 12)
    have b14709 := hb (x 15 12)
    have b14710 := hb (x 15 1 && x 15 12)
    clear * - r14708 b14709 b14710 d14699
    omega
  have d14711 : (x 15 2 && x 15 12).toNat = 0 := by
    have r14712 := hand2 (x 15 2) (x 15 12)
    have b14713 := hb (x 15 12)
    have b14714 := hb (x 15 2 && x 15 12)
    clear * - r14712 b14713 b14714 d14699
    omega
  have d14715 : (x 14 13).toNat = 0 := by
    have r14716 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
    have e14717 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e14718 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b14719 := hb (x 12 3)
    have b14720 := hb (x 13 2)
    have b14721 := hb (x 14 13)
    have b14722 := hb (x 15 12)
    clear * - r14716 e14717 e14718 b14719 b14720 b14721 b14722 d14699 d14695
    omega
  have d14723 : (x 14 2 && x 14 13).toNat = 0 := by
    have r14724 := hand2 (x 14 2) (x 14 13)
    have b14725 := hb (x 14 13)
    have b14726 := hb (x 14 2 && x 14 13)
    clear * - r14724 b14725 b14726 d14715
    omega
  have d14727 : (x 14 3 && x 14 13).toNat = 0 := by
    have r14728 := hand2 (x 14 3) (x 14 13)
    have b14729 := hb (x 14 13)
    have b14730 := hb (x 14 3 && x 14 13)
    clear * - r14728 b14729 b14730 d14715
    omega
  have d14731 : (x 13 1 && x 13 14).toNat = 1 := by
    have r14732 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
    have b14733 := hb (x 12 2)
    have b14734 := hb (x 14 13)
    have b14735 := hb (x 13 1 && x 13 14)
    clear * - r14732 b14733 b14734 b14735 d14715 d14543
    omega
  have d14736 : (x 13 1).toNat = 1 := by
    have r14737 := hand1 (x 13 1) (x 13 14)
    have b14738 := hb (x 13 1)
    have b14739 := hb (x 13 1 && x 13 14)
    clear * - r14737 b14738 b14739 d14731
    omega
  have d14740 : (x 14 14).toNat = 0 := by
    have r14741 : (x 14 14).toNat + (x 13 1).toNat = 1 := hd14 14
    have b14742 := hb (x 13 1)
    have b14743 := hb (x 14 14)
    clear * - r14741 b14742 b14743 d14736
    omega
  have d14744 : (x 14 1 && x 14 14).toNat = 0 := by
    have r14745 := hand2 (x 14 1) (x 14 14)
    have b14746 := hb (x 14 14)
    have b14747 := hb (x 14 1 && x 14 14)
    clear * - r14745 b14746 b14747 d14740
    omega
  have d14748 : (x 14 2).toNat = 0 := by
    have r14749 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
    have b14750 := hb (x 14 2)
    have b14751 := hb (x 14 14)
    clear * - r14749 b14750 b14751 d14740
    omega
  have d14752 : (x 13 2).toNat = 0 := by
    have r14753 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
    have e14754 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
    have e14755 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
    have b14756 := hb (x 12 3)
    have b14757 := hb (x 13 2)
    have b14758 := hb (x 14 13)
    have b14759 := hb (x 15 12)
    clear * - r14753 e14754 e14755 b14756 b14757 b14758 b14759 d14699 d14715 d14695
    omega
  have d14760 : (x 15 13).toNat = 1 := by
    have r14761 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
    have b14762 := hb (x 13 2)
    have b14763 := hb (x 15 13)
    have b14764 := hb (x 14 1 && x 14 14)
    clear * - r14761 b14762 b14763 b14764 d14744 d14752
    omega
  have d14765 : (x 16 12).toNat = 0 := by
    have r14766 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
    have e14767 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e14768 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b14769 := hb (x 13 3)
    have b14770 := hb (x 14 2)
    have b14771 := hb (x 15 13)
    have b14772 := hb (x 16 12)
    clear * - r14766 e14767 e14768 b14769 b14770 b14771 b14772 d14760 d14748
    omega
  have d14773 : (x 13 3).toNat = 0 := by
    have r14774 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
    have e14775 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e14776 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b14777 := hb (x 13 3)
    have b14778 := hb (x 14 2)
    have b14779 := hb (x 15 13)
    have b14780 := hb (x 16 12)
    clear * - r14774 e14775 e14776 b14777 b14778 b14779 b14780 d14765 d14760 d14748
    omega
  have d14781 : (x 13 3 && x 13 14).toNat = 0 := by
    have r14782 := hand1 (x 13 3) (x 13 14)
    have b14783 := hb (x 13 3)
    have b14784 := hb (x 13 3 && x 13 14)
    clear * - r14782 b14783 b14784 d14773
    omega
  have d14785 : (x 16 11).toNat = 1 := by
    have r14786 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := hcov11 16
    have b14787 := hb (x 12 4)
    have b14788 := hb (x 16 11)
    have b14789 := hb (x 15 1 && x 15 12)
    have b14790 := hb (x 14 2 && x 14 13)
    have b14791 := hb (x 13 3 && x 13 14)
    clear * - r14786 b14787 b14788 b14789 b14790 b14791 d14707 d14723 d14781 d14672
    omega
  have d14792 : (x 16 3).toNat = 1 := by
    have r14793 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
    have b14794 := hb (x 16 3)
    have b14795 := hb (x 16 11)
    clear * - r14793 b14794 b14795 d14785
    omega
  have d14796 : (x 19 12).toNat = 0 := by
    have r14797 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
    have e14798 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e14799 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b14800 := hb (x 16 3)
    have b14801 := hb (x 17 2)
    have b14802 := hb (x 18 13)
    have b14803 := hb (x 19 12)
    clear * - r14797 e14798 e14799 b14800 b14801 b14802 b14803 d14792
    omega
  have d14804 : (x 18 13).toNat = 0 := by
    have r14805 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
    have e14806 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e14807 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b14808 := hb (x 16 3)
    have b14809 := hb (x 17 2)
    have b14810 := hb (x 18 13)
    have b14811 := hb (x 19 12)
    clear * - r14805 e14806 e14807 b14808 b14809 b14810 b14811 d14796 d14792
    omega
  have d14812 : (x 17 1 && x 17 14).toNat = 1 := by
    have r14813 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := hcov13 18
    have b14814 := hb (x 16 2)
    have b14815 := hb (x 18 13)
    have b14816 := hb (x 17 1 && x 17 14)
    clear * - r14813 b14814 b14815 b14816 d14804 d14656
    omega
  have d14817 : (x 17 14).toNat = 1 := by
    have r14818 := hand2 (x 17 1) (x 17 14)
    have b14819 := hb (x 17 14)
    have b14820 := hb (x 17 1 && x 17 14)
    clear * - r14818 b14819 b14820 d14812
    omega
  have d14821 : (x 16 1).toNat = 0 := by
    have r14822 : (x 17 14).toNat + (x 16 1).toNat = 1 := hd14 17
    have b14823 := hb (x 16 1)
    have b14824 := hb (x 17 14)
    clear * - r14822 b14823 b14824 d14817
    omega
  have d14825 : (x 16 1 && x 16 11).toNat = 0 := by
    have r14826 := hand1 (x 16 1) (x 16 11)
    have b14827 := hb (x 16 1)
    have b14828 := hb (x 16 1 && x 16 11)
    clear * - r14826 b14827 b14828 d14821
    omega
  have d14829 : (x 17 2).toNat = 0 := by
    have r14830 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
    have e14831 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e14832 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have b14833 := hb (x 16 3)
    have b14834 := hb (x 17 2)
    have b14835 := hb (x 18 13)
    have b14836 := hb (x 19 12)
    clear * - r14830 e14831 e14832 b14833 b14834 b14835 b14836 d14796 d14804 d14792
    omega
  have d14837 : (x 17 10).toNat = 0 := by
    have r14838 : (x 17 10).toNat ≤ (x 17 2).toNat := himp _ _ (hp10 17)
    have b14839 := hb (x 17 2)
    have b14840 := hb (x 17 10)
    clear * - r14838 b14839 b14840 d14829
    omega
  have r14841 : 1 ≤ (x 17 10).toNat + (x 16 1 && x 16 11).toNat + (x 15 2 && x 15 12).toNat + (x 14 3 && x 14 13).toNat + (x 13 4 && x 13 14).toNat + (x 12 5).toNat := hcov10 17
  have b14842 := hb (x 12 5)
  have b14843 := hb (x 17 10)
  have b14844 := hb (x 16 1 && x 16 11)
  have b14845 := hb (x 15 2 && x 15 12)
  have b14846 := hb (x 14 3 && x 14 13)
  have b14847 := hb (x 13 4 && x 13 14)
  linarith only [r14841, b14842, b14843, b14844, b14845, b14846, b14847, d14837, d14825, d14711, d14727, d14609, d14621]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 2).toNat = 0)
    (g1 : (x 0 3).toNat = 1)
    (g2 : (x 0 4).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_b0001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2
