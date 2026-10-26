import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0001

Topic: combinatorics   Node: cd2c8df6badc

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 28 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0001_aux (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x 0 5).toNat = 0)
    (g2 : (x 0 6).toNat = 0)
    (g3 : (x 0 7).toNat = 1)
    (g4 : (x 0 8).toNat = 0)
    (g5 : (x 0 10).toNat = 0)
    (g6 : (x 0 13).toNat = 0)
    (g7 : (x 1 6).toNat = 0)
    (g8 : (x 3 2).toNat = 0)
    (g9 : (x 3 4).toNat = 0)
    (g10 : (x 3 6).toNat = 0)
    (g11 : (x 3 10).toNat = 0)
    (g12 : (x 3 6 && x 3 10).toNat = 0)
    (g13 : (x 0 9 && x 0 13).toNat = 0)
    (g14 : (x 3 7 && x 3 12).toNat = 0)
    (g15 : (x 1 9 && x 1 14).toNat = 0)
    (g16 : (x 3 5 && x 3 12).toNat = 0)
    (g17 : (x 1 7 && x 1 14).toNat = 0)
    (g18 : (x 0 1 && x 0 10).toNat = 0)
    (g19 : (x 3 3 && x 3 12).toNat = 0)
    (g20 : (x 1 5 && x 1 14).toNat = 0)
    (g21 : (x 3 4 && x 3 13).toNat = 0)
    (g22 : (x 3 2 && x 3 12).toNat = 0)
    (g23 : (x 1 4 && x 1 14).toNat = 0)
    (g24 : (x 3 4 && x 3 14).toNat = 0)
    (g25 : (x 0 2 && x 0 13).toNat = 0)
    (g26 : (x 0 1 && x 0 14).toNat = 0)
    (g27 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d41197 : (x 7 8).toNat = 0 := by
    have r41198 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e41199 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e41200 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e41201 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e41202 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e41203 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e41204 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b41205 := hb (x 0 7)
    have b41206 := hb (x 1 6)
    have b41207 := hb (x 2 5)
    have b41208 := hb (x 3 4)
    have b41209 := hb (x 4 11)
    have b41210 := hb (x 5 10)
    have b41211 := hb (x 6 9)
    have b41212 := hb (x 7 8)
    clear * - r41198 e41199 e41200 e41201 e41202 e41203 e41204 b41205 b41206 b41207 b41208 b41209 b41210 b41211 b41212 g9 g7 g3
    omega
  have d41213 : (x 7 1 && x 7 8).toNat = 0 := by
    have r41214 := hand2 (x 7 1) (x 7 8)
    have b41215 := hb (x 7 8)
    have b41216 := hb (x 7 1 && x 7 8)
    clear * - r41214 b41215 b41216 d41197
    omega
  have d41217 : (x 7 3 && x 7 8).toNat = 0 := by
    have r41218 := hand2 (x 7 3) (x 7 8)
    have b41219 := hb (x 7 8)
    have b41220 := hb (x 7 3 && x 7 8)
    clear * - r41218 b41219 b41220 d41197
    omega
  have d41221 : (x 6 9).toNat = 0 := by
    have r41222 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e41223 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e41224 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e41225 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e41226 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e41227 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e41228 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b41229 := hb (x 0 7)
    have b41230 := hb (x 1 6)
    have b41231 := hb (x 2 5)
    have b41232 := hb (x 3 4)
    have b41233 := hb (x 4 11)
    have b41234 := hb (x 5 10)
    have b41235 := hb (x 6 9)
    have b41236 := hb (x 7 8)
    clear * - r41222 e41223 e41224 e41225 e41226 e41227 e41228 b41229 b41230 b41231 b41232 b41233 b41234 b41235 b41236 d41197 g9 g7 g3
    omega
  have d41237 : (x 6 2 && x 6 9).toNat = 0 := by
    have r41238 := hand2 (x 6 2) (x 6 9)
    have b41239 := hb (x 6 9)
    have b41240 := hb (x 6 2 && x 6 9)
    clear * - r41238 b41239 b41240 d41221
    omega
  have d41241 : (x 6 4 && x 6 9).toNat = 0 := by
    have r41242 := hand2 (x 6 4) (x 6 9)
    have b41243 := hb (x 6 9)
    have b41244 := hb (x 6 4 && x 6 9)
    clear * - r41242 b41243 b41244 d41221
    omega
  have d41245 : (x 5 10).toNat = 0 := by
    have r41246 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e41247 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e41248 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e41249 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e41250 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e41251 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e41252 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b41253 := hb (x 0 7)
    have b41254 := hb (x 1 6)
    have b41255 := hb (x 2 5)
    have b41256 := hb (x 3 4)
    have b41257 := hb (x 4 11)
    have b41258 := hb (x 5 10)
    have b41259 := hb (x 6 9)
    have b41260 := hb (x 7 8)
    clear * - r41246 e41247 e41248 e41249 e41250 e41251 e41252 b41253 b41254 b41255 b41256 b41257 b41258 b41259 b41260 d41197 d41221 g9 g7 g3
    omega
  have d41261 : (x 5 1 && x 5 10).toNat = 0 := by
    have r41262 := hand2 (x 5 1) (x 5 10)
    have b41263 := hb (x 5 10)
    have b41264 := hb (x 5 1 && x 5 10)
    clear * - r41262 b41263 b41264 d41245
    omega
  have d41265 : (x 5 3 && x 5 10).toNat = 0 := by
    have r41266 := hand2 (x 5 3) (x 5 10)
    have b41267 := hb (x 5 10)
    have b41268 := hb (x 5 3 && x 5 10)
    clear * - r41266 b41267 b41268 d41245
    omega
  have d41269 : (x 5 5 && x 5 10).toNat = 0 := by
    have r41270 := hand2 (x 5 5) (x 5 10)
    have b41271 := hb (x 5 10)
    have b41272 := hb (x 5 5 && x 5 10)
    clear * - r41270 b41271 b41272 d41245
    omega
  have d41273 : (x 4 11).toNat = 0 := by
    have r41274 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e41275 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e41276 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e41277 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e41278 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e41279 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e41280 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b41281 := hb (x 0 7)
    have b41282 := hb (x 1 6)
    have b41283 := hb (x 2 5)
    have b41284 := hb (x 3 4)
    have b41285 := hb (x 4 11)
    have b41286 := hb (x 5 10)
    have b41287 := hb (x 6 9)
    have b41288 := hb (x 7 8)
    clear * - r41274 e41275 e41276 e41277 e41278 e41279 e41280 b41281 b41282 b41283 b41284 b41285 b41286 b41287 b41288 d41197 d41221 d41245 g9 g7 g3
    omega
  have d41289 : (x 4 1 && x 4 11).toNat = 0 := by
    have r41290 := hand2 (x 4 1) (x 4 11)
    have b41291 := hb (x 4 11)
    have b41292 := hb (x 4 1 && x 4 11)
    clear * - r41290 b41291 b41292 d41273
    omega
  have d41293 : (x 2 3 && x 2 13).toNat = 1 := by
    have r41294 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := hcov10 5
    have b41295 := hb (x 0 5)
    have b41296 := hb (x 5 10)
    have b41297 := hb (x 4 1 && x 4 11)
    have b41298 := hb (x 3 2 && x 3 12)
    have b41299 := hb (x 2 3 && x 2 13)
    have b41300 := hb (x 1 4 && x 1 14)
    clear * - r41294 b41295 b41296 b41297 b41298 b41299 b41300 d41245 d41289 g22 g23 g1
    omega
  have d41301 : (x 2 3).toNat = 1 := by
    have r41302 := hand1 (x 2 3) (x 2 13)
    have b41303 := hb (x 2 3)
    have b41304 := hb (x 2 3 && x 2 13)
    clear * - r41302 b41303 b41304 d41293
    omega
  have d41305 : (x 5 12).toNat = 0 := by
    have r41306 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
    have e41307 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e41308 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b41309 := hb (x 2 3)
    have b41310 := hb (x 3 2)
    have b41311 := hb (x 4 13)
    have b41312 := hb (x 5 12)
    clear * - r41306 e41307 e41308 b41309 b41310 b41311 b41312 g8 d41301
    omega
  have d41313 : (x 5 2 && x 5 12).toNat = 0 := by
    have r41314 := hand2 (x 5 2) (x 5 12)
    have b41315 := hb (x 5 12)
    have b41316 := hb (x 5 2 && x 5 12)
    clear * - r41314 b41315 b41316 d41305
    omega
  have d41317 : (x 5 4).toNat = 0 := by
    have r41318 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b41319 := hb (x 5 4)
    have b41320 := hb (x 5 12)
    clear * - r41318 b41319 b41320 d41305
    omega
  have d41321 : (x 5 4 && x 5 8).toNat = 0 := by
    have r41322 := hand1 (x 5 4) (x 5 8)
    have b41323 := hb (x 5 4)
    have b41324 := hb (x 5 4 && x 5 8)
    clear * - r41322 b41323 b41324 d41317
    omega
  have d41325 : (x 4 13).toNat = 0 := by
    have r41326 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
    have e41327 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e41328 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b41329 := hb (x 2 3)
    have b41330 := hb (x 3 2)
    have b41331 := hb (x 4 13)
    have b41332 := hb (x 5 12)
    clear * - r41326 e41327 e41328 b41329 b41330 b41331 b41332 d41305 g8 d41301
    omega
  have d41333 : (x 4 3 && x 4 13).toNat = 0 := by
    have r41334 := hand2 (x 4 3) (x 4 13)
    have b41335 := hb (x 4 13)
    have b41336 := hb (x 4 3 && x 4 13)
    clear * - r41334 b41335 b41336 d41325
    omega
  have d41337 : (x 4 5).toNat = 0 := by
    have r41338 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
    have b41339 := hb (x 4 5)
    have b41340 := hb (x 4 13)
    clear * - r41338 b41339 b41340 d41325
    omega
  have d41341 : (x 4 5 && x 4 9).toNat = 0 := by
    have r41342 := hand1 (x 4 5) (x 4 9)
    have b41343 := hb (x 4 5)
    have b41344 := hb (x 4 5 && x 4 9)
    clear * - r41342 b41343 b41344 d41337
    omega
  have d41345 : (x 2 2).toNat = 1 := by
    have r41346 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
    have b41347 := hb (x 2 2)
    have b41348 := hb (x 4 13)
    have b41349 := hb (x 3 1 && x 3 14)
    clear * - r41346 b41347 b41348 b41349 d41325 g27
    omega
  have d41350 : (x 2 14).toNat = 1 := by
    have r41351 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
    have b41352 := hb (x 2 2)
    have b41353 := hb (x 2 14)
    clear * - r41351 b41352 b41353 d41345
    omega
  have d41354 : (x 1 1).toNat = 0 := by
    have r41355 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
    have b41356 := hb (x 1 1)
    have b41357 := hb (x 2 14)
    clear * - r41355 b41356 b41357 d41350
    omega
  have d41358 : (x 1 1 && x 1 12).toNat = 0 := by
    have r41359 := hand1 (x 1 1) (x 1 12)
    have b41360 := hb (x 1 1)
    have b41361 := hb (x 1 1 && x 1 12)
    clear * - r41359 b41360 b41361 d41354
    omega
  have d41362 : (x 1 13).toNat = 0 := by
    have r41363 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
    have b41364 := hb (x 1 1)
    have b41365 := hb (x 1 13)
    clear * - r41363 b41364 b41365 d41354
    omega
  have d41366 : (x 1 9 && x 1 13).toNat = 0 := by
    have r41367 := hand2 (x 1 9) (x 1 13)
    have b41368 := hb (x 1 13)
    have b41369 := hb (x 1 9 && x 1 13)
    clear * - r41367 b41368 b41369 d41362
    omega
  have d41370 : (x 1 5).toNat = 0 := by
    have r41371 : (x 1 5).toNat ≤ (x 1 13).toNat := himp _ _ (hp5 1)
    have b41372 := hb (x 1 5)
    have b41373 := hb (x 1 13)
    clear * - r41371 b41372 b41373 d41362
    omega
  have d41374 : (x (-1) 2).toNat = 1 := by
    have r41375 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
    have b41376 := hb (x (-1) 2)
    have b41377 := hb (x 1 13)
    have b41378 := hb (x 0 1 && x 0 14)
    clear * - r41375 b41376 b41377 b41378 d41362 g26
    omega
  have d41379 : (x (-1) 14).toNat = 1 := by
    have r41380 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
    have b41381 := hb (x (-1) 2)
    have b41382 := hb (x (-1) 14)
    clear * - r41380 b41381 b41382 d41374
    omega
  have d41383 : (x 1 12).toNat = 0 := by
    have r41384 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
    have e41385 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e41386 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b41387 := hb (x (-2) 3)
    have b41388 := hb (x (-1) 2)
    have b41389 := hb (x 0 13)
    have b41390 := hb (x 1 12)
    clear * - r41384 e41385 e41386 b41387 b41388 b41389 b41390 g6 d41374
    omega
  have d41391 : (x 1 8 && x 1 12).toNat = 0 := by
    have r41392 := hand2 (x 1 8) (x 1 12)
    have b41393 := hb (x 1 12)
    have b41394 := hb (x 1 8 && x 1 12)
    clear * - r41392 b41393 b41394 d41383
    omega
  have d41395 : (x (-2) 3).toNat = 0 := by
    have r41396 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
    have e41397 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
    have e41398 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
    have b41399 := hb (x (-2) 3)
    have b41400 := hb (x (-1) 2)
    have b41401 := hb (x 0 13)
    have b41402 := hb (x 1 12)
    clear * - r41396 e41397 e41398 b41399 b41400 b41401 b41402 d41383 g6 d41374
    omega
  have d41403 : (x (-2) 3 && x (-2) 12).toNat = 0 := by
    have r41404 := hand1 (x (-2) 3) (x (-2) 12)
    have b41405 := hb (x (-2) 3)
    have b41406 := hb (x (-2) 3 && x (-2) 12)
    clear * - r41404 b41405 b41406 d41395
    omega
  have d41407 : (x (-2) 11).toNat = 0 := by
    have r41408 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
    have b41409 := hb (x (-2) 3)
    have b41410 := hb (x (-2) 11)
    clear * - r41408 b41409 b41410 d41395
    omega
  have d41411 : (x 1 9).toNat = 0 := by
    have r41412 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
    have b41413 := hb (x 1 1)
    have b41414 := hb (x 1 9)
    clear * - r41412 b41413 b41414 d41354
    omega
  have d41415 : (x 4 12).toNat = 0 := by
    have r41416 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
    have e41417 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e41418 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b41419 := hb (x 1 3)
    have b41420 := hb (x 2 2)
    have b41421 := hb (x 3 13)
    have b41422 := hb (x 4 12)
    clear * - r41416 e41417 e41418 b41419 b41420 b41421 b41422 d41345
    omega
  have d41423 : (x 4 3 && x 4 12).toNat = 0 := by
    have r41424 := hand2 (x 4 3) (x 4 12)
    have b41425 := hb (x 4 12)
    have b41426 := hb (x 4 3 && x 4 12)
    clear * - r41424 b41425 b41426 d41415
    omega
  have d41427 : (x 4 4).toNat = 0 := by
    have r41428 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b41429 := hb (x 4 4)
    have b41430 := hb (x 4 12)
    clear * - r41428 b41429 b41430 d41415
    omega
  have d41431 : (x 4 4 && x 4 11).toNat = 0 := by
    have r41432 := hand1 (x 4 4) (x 4 11)
    have b41433 := hb (x 4 4)
    have b41434 := hb (x 4 4 && x 4 11)
    clear * - r41432 b41433 b41434 d41427
    omega
  have d41435 : (x 3 13).toNat = 0 := by
    have r41436 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
    have e41437 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e41438 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b41439 := hb (x 1 3)
    have b41440 := hb (x 2 2)
    have b41441 := hb (x 3 13)
    have b41442 := hb (x 4 12)
    clear * - r41436 e41437 e41438 b41439 b41440 b41441 b41442 d41415 d41345
    omega
  have d41443 : (x 3 5).toNat = 0 := by
    have r41444 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
    have b41445 := hb (x 3 5)
    have b41446 := hb (x 3 13)
    clear * - r41444 b41445 b41446 d41435
    omega
  have d41447 : (x 4 2 && x 4 11).toNat = 0 := by
    have r41448 := hand2 (x 4 2) (x 4 11)
    have b41449 := hb (x 4 11)
    have b41450 := hb (x 4 2 && x 4 11)
    clear * - r41448 b41449 b41450 d41273
    omega
  have d41451 : (x 2 4 && x 2 13).toNat = 1 := by
    have r41452 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := hcov9 6
    have b41453 := hb (x 0 6)
    have b41454 := hb (x 6 9)
    have b41455 := hb (x 5 1 && x 5 10)
    have b41456 := hb (x 4 2 && x 4 11)
    have b41457 := hb (x 3 3 && x 3 12)
    have b41458 := hb (x 2 4 && x 2 13)
    have b41459 := hb (x 1 5 && x 1 14)
    clear * - r41452 b41453 b41454 b41455 b41456 b41457 b41458 b41459 d41221 d41261 d41447 g19 g20 g2
    omega
  have d41460 : (x 2 4).toNat = 1 := by
    have r41461 := hand1 (x 2 4) (x 2 13)
    have b41462 := hb (x 2 4)
    have b41463 := hb (x 2 4 && x 2 13)
    clear * - r41461 b41462 b41463 d41451
    omega
  have d41464 : (x 2 12).toNat = 1 := by
    have r41465 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b41466 := hb (x 2 4)
    have b41467 := hb (x 2 12)
    clear * - r41465 b41466 b41467 d41460
    omega
  have d41468 : (x (-1) 3).toNat = 0 := by
    have r41469 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
    have e41470 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e41471 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b41472 := hb (x (-1) 3)
    have b41473 := hb (x 0 2)
    have b41474 := hb (x 1 13)
    have b41475 := hb (x 2 12)
    clear * - r41469 e41470 e41471 b41472 b41473 b41474 b41475 d41464 d41362 g0
    omega
  have d41476 : (x (-1) 3 && x (-1) 14).toNat = 0 := by
    have r41477 := hand1 (x (-1) 3) (x (-1) 14)
    have b41478 := hb (x (-1) 3)
    have b41479 := hb (x (-1) 3 && x (-1) 14)
    clear * - r41477 b41478 b41479 d41468
    omega
  have d41480 : (x (-1) 11).toNat = 0 := by
    have r41481 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
    have b41482 := hb (x (-1) 3)
    have b41483 := hb (x (-1) 11)
    clear * - r41481 b41482 b41483 d41468
    omega
  have d41484 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
    have r41485 := hand2 (x (-1) 2) (x (-1) 11)
    have b41486 := hb (x (-1) 11)
    have b41487 := hb (x (-1) 2 && x (-1) 11)
    clear * - r41485 b41486 b41487 d41480
    omega
  have d41488 : (x 4 6 && x 4 11).toNat = 0 := by
    have r41489 := hand2 (x 4 6) (x 4 11)
    have b41490 := hb (x 4 11)
    have b41491 := hb (x 4 6 && x 4 11)
    clear * - r41489 b41490 b41491 d41273
    omega
  have d41492 : (x 2 5).toNat = 0 := by
    have r41493 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
    have e41494 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e41495 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e41496 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e41497 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e41498 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e41499 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b41500 := hb (x 0 7)
    have b41501 := hb (x 1 6)
    have b41502 := hb (x 2 5)
    have b41503 := hb (x 3 4)
    have b41504 := hb (x 4 11)
    have b41505 := hb (x 5 10)
    have b41506 := hb (x 6 9)
    have b41507 := hb (x 7 8)
    clear * - r41493 e41494 e41495 e41496 e41497 e41498 e41499 b41500 b41501 b41502 b41503 b41504 b41505 b41506 b41507 d41197 d41221 d41245 d41273 g9 g7 g3
    omega
  have d41508 : (x 2 5 && x 2 14).toNat = 0 := by
    have r41509 := hand1 (x 2 5) (x 2 14)
    have b41510 := hb (x 2 5)
    have b41511 := hb (x 2 5 && x 2 14)
    clear * - r41509 b41510 b41511 d41492
    omega
  have d41512 : (x 6 8).toNat = 0 := by
    have r41513 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
    have e41514 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e41515 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e41516 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e41517 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e41518 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e41519 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b41520 := hb (x (-1) 7)
    have b41521 := hb (x 0 6)
    have b41522 := hb (x 1 5)
    have b41523 := hb (x 2 4)
    have b41524 := hb (x 3 11)
    have b41525 := hb (x 4 10)
    have b41526 := hb (x 5 9)
    have b41527 := hb (x 6 8)
    clear * - r41513 e41514 e41515 e41516 e41517 e41518 e41519 b41520 b41521 b41522 b41523 b41524 b41525 b41526 b41527 d41460 d41370 g2
    omega
  have d41528 : (x 6 4 && x 6 8).toNat = 0 := by
    have r41529 := hand2 (x 6 4) (x 6 8)
    have b41530 := hb (x 6 8)
    have b41531 := hb (x 6 4 && x 6 8)
    clear * - r41529 b41530 b41531 d41512
    omega
  have d41532 : (x 5 9).toNat = 0 := by
    have r41533 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
    have e41534 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e41535 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e41536 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e41537 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e41538 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e41539 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b41540 := hb (x (-1) 7)
    have b41541 := hb (x 0 6)
    have b41542 := hb (x 1 5)
    have b41543 := hb (x 2 4)
    have b41544 := hb (x 3 11)
    have b41545 := hb (x 4 10)
    have b41546 := hb (x 5 9)
    have b41547 := hb (x 6 8)
    clear * - r41533 e41534 e41535 e41536 e41537 e41538 e41539 b41540 b41541 b41542 b41543 b41544 b41545 b41546 b41547 d41512 d41460 d41370 g2
    omega
  have d41548 : (x 5 5 && x 5 9).toNat = 0 := by
    have r41549 := hand2 (x 5 5) (x 5 9)
    have b41550 := hb (x 5 9)
    have b41551 := hb (x 5 5 && x 5 9)
    clear * - r41549 b41550 b41551 d41532
    omega
  have d41552 : (x 4 10).toNat = 0 := by
    have r41553 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
    have e41554 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e41555 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e41556 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e41557 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e41558 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e41559 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b41560 := hb (x (-1) 7)
    have b41561 := hb (x 0 6)
    have b41562 := hb (x 1 5)
    have b41563 := hb (x 2 4)
    have b41564 := hb (x 3 11)
    have b41565 := hb (x 4 10)
    have b41566 := hb (x 5 9)
    have b41567 := hb (x 6 8)
    clear * - r41553 e41554 e41555 e41556 e41557 e41558 e41559 b41560 b41561 b41562 b41563 b41564 b41565 b41566 b41567 d41512 d41532 d41460 d41370 g2
    omega
  have d41568 : (x 4 6 && x 4 10).toNat = 0 := by
    have r41569 := hand2 (x 4 6) (x 4 10)
    have b41570 := hb (x 4 10)
    have b41571 := hb (x 4 6 && x 4 10)
    clear * - r41569 b41570 b41571 d41552
    omega
  have d41572 : (x 3 11).toNat = 0 := by
    have r41573 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := hd8 6
    have e41574 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e41575 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e41576 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e41577 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e41578 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e41579 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b41580 := hb (x (-1) 7)
    have b41581 := hb (x 0 6)
    have b41582 := hb (x 1 5)
    have b41583 := hb (x 2 4)
    have b41584 := hb (x 3 11)
    have b41585 := hb (x 4 10)
    have b41586 := hb (x 5 9)
    have b41587 := hb (x 6 8)
    clear * - r41573 e41574 e41575 e41576 e41577 e41578 e41579 b41580 b41581 b41582 b41583 b41584 b41585 b41586 b41587 d41512 d41532 d41552 d41460 d41370 g2
    omega
  have d41588 : (x 3 7 && x 3 11).toNat = 0 := by
    have r41589 := hand2 (x 3 7) (x 3 11)
    have b41590 := hb (x 3 11)
    have b41591 := hb (x 3 7 && x 3 11)
    clear * - r41589 b41590 b41591 d41572
    omega
  have r41592 : (x 12 1).toNat + (x 11 2).toNat + (x 10 3).toNat + (x 9 4).toNat + (x 8 5).toNat + (x 7 6).toNat + (x 6 7).toNat + (x 5 8).toNat + (x 4 9).toNat + (x 3 10).toNat + (x 2 11).toNat + (x 1 12).toNat + (x 0 13).toNat + (x (-1) 14).toNat = 3 := hcount 13
  have r41593 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
  have e41594 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
  have e41595 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
  have e41596 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
  have e41597 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
  have e41598 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
  have e41599 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
  have r41600 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := hd8 2
  have e41601 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
  have e41602 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
  have e41603 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
  have e41604 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
  have e41605 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
  have e41606 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
  have r41607 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := hd8 8
  have e41608 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
  have e41609 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
  have e41610 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
  have e41611 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
  have e41612 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
  have e41613 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
  have r41614 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := hd8 9
  have e41615 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
  have e41616 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
  have e41617 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
  have e41618 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
  have e41619 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
  have e41620 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
  have r41621 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := hd8 14
  have e41622 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
  have e41623 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
  have e41624 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
  have e41625 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
  have e41626 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
  have e41627 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
  have r41628 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := hd8 15
  have e41629 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
  have e41630 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
  have e41631 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
  have e41632 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
  have e41633 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
  have e41634 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
  have r41635 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := hd12 8
  have e41636 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
  have e41637 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
  have r41638 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
  have e41639 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
  have e41640 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
  have r41641 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
  have e41642 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
  have e41643 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
  have r41644 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
  have r41645 : 1 ≤ (x 9 4).toNat + (x 8 1 && x 8 5).toNat + (x 7 2 && x 7 6).toNat + (x 6 3 && x 6 7).toNat + (x 5 4 && x 5 8).toNat + (x 4 5 && x 4 9).toNat + (x 3 6 && x 3 10).toNat + (x 2 7 && x 2 11).toNat + (x 1 8 && x 1 12).toNat + (x 0 9 && x 0 13).toNat + (x (-1) 10 && x (-1) 14).toNat + (x (-2) 11).toNat := hcov4 9
  have e41646 : (x 8 1 && x 8 5).toNat = (x 8 5).toNat := handr _ _ (fun h => hp13 8 (hp5 8 (h)))
  have e41647 : (x (-1) 10 && x (-1) 14).toNat = (x (-1) 10).toNat := handl _ _ (fun h => hp2 (-1) (hp10 (-1) (h)))
  have r41648 : 1 ≤ (x 10 4).toNat + (x 9 1 && x 9 5).toNat + (x 8 2 && x 8 6).toNat + (x 7 3 && x 7 7).toNat + (x 6 4 && x 6 8).toNat + (x 5 5 && x 5 9).toNat + (x 4 6 && x 4 10).toNat + (x 3 7 && x 3 11).toNat + (x 2 8 && x 2 12).toNat + (x 1 9 && x 1 13).toNat + (x 0 10 && x 0 14).toNat + (x (-1) 11).toNat := hcov4 10
  have e41649 : (x 9 1 && x 9 5).toNat = (x 9 5).toNat := handr _ _ (fun h => hp13 9 (hp5 9 (h)))
  have e41650 : (x 0 10 && x 0 14).toNat = (x 0 10).toNat := handl _ _ (fun h => hp2 0 (hp10 0 (h)))
  have r41651 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := hcov5 10
  have r41652 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := hcov7 8
  have r41653 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := hcov9 1
  have r41654 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := hcov9 7
  have r41655 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := hcov10 7
  have r41656 : 1 ≤ (x 12 10).toNat + (x 11 1 && x 11 11).toNat + (x 10 2 && x 10 12).toNat + (x 9 3 && x 9 13).toNat + (x 8 4 && x 8 14).toNat + (x 7 5).toNat := hcov10 12
  have r41657 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := hcov10 13
  have r41658 : 1 ≤ (x 2 11).toNat + (x 1 1 && x 1 12).toNat + (x 0 2 && x 0 13).toNat + (x (-1) 3 && x (-1) 14).toNat + (x (-2) 4).toNat := hcov11 2
  have r41659 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
  have r41660 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
  have r41661 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
  have r41662 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
  have r41663 : (x 7 9).toNat ≤ (x 7 1).toNat := himp _ _ (hp9 7)
  have r41664 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
  have r41665 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
  have r41666 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
  have r41667 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
  have r41668 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
  have r41669 := hand2 (x 7 2) (x 7 6)
  have r41670 := hand2 (x 6 3) (x 6 7)
  have r41671 := hand1 (x 2 7) (x 2 11)
  have r41672 := hand2 (x 8 2) (x 8 6)
  have r41673 := hand1 (x 7 3) (x 7 7)
  have r41674 := hand1 (x 2 8) (x 2 12)
  have r41675 := hand2 (x 9 1) (x 9 6)
  have r41676 := hand1 (x 8 2) (x 8 7)
  have r41677 := hand1 (x 2 8) (x 2 13)
  have r41678 := hand1 (x 2 6) (x 2 13)
  have r41679 := hand1 (x (-3) 4) (x (-3) 13)
  have r41680 := hand1 (x (-4) 5) (x (-4) 14)
  have r41681 := hand2 (x 6 1) (x 6 10)
  have r41682 := hand2 (x 5 2) (x 5 11)
  have r41683 := hand2 (x 6 1) (x 6 11)
  have r41684 := hand2 (x 11 1) (x 11 11)
  have r41685 := hand2 (x 10 2) (x 10 12)
  have r41686 := hand2 (x 9 3) (x 9 13)
  have r41687 := hand1 (x 8 4) (x 8 14)
  have r41688 := hand1 (x 12 1) (x 12 11)
  have r41689 := hand1 (x 11 2) (x 11 12)
  have r41690 := hand1 (x 10 3) (x 10 13)
  have r41691 := hand1 (x 9 4) (x 9 14)
  have b41692 := hb (x (-6) 7)
  have b41693 := hb (x (-5) 6)
  have b41694 := hb (x (-5) 7)
  have b41695 := hb (x (-4) 5)
  have b41696 := hb (x (-4) 6)
  have b41697 := hb (x (-3) 4)
  have b41698 := hb (x (-3) 5)
  have b41699 := hb (x (-2) 4)
  have b41700 := hb (x (-2) 11)
  have b41701 := hb (x (-1) 10)
  have b41702 := hb (x (-1) 11)
  have b41703 := hb (x (-1) 14)
  have b41704 := hb (x 0 8)
  have b41705 := hb (x 0 9)
  have b41706 := hb (x 0 10)
  have b41707 := hb (x 0 13)
  have b41708 := hb (x 1 6)
  have b41709 := hb (x 1 7)
  have b41710 := hb (x 1 8)
  have b41711 := hb (x 1 9)
  have b41712 := hb (x 1 12)
  have b41713 := hb (x 2 5)
  have b41714 := hb (x 2 6)
  have b41715 := hb (x 2 7)
  have b41716 := hb (x 2 8)
  have b41717 := hb (x 2 11)
  have b41718 := hb (x 3 5)
  have b41719 := hb (x 3 6)
  have b41720 := hb (x 3 10)
  have b41721 := hb (x 4 4)
  have b41722 := hb (x 4 5)
  have b41723 := hb (x 4 9)
  have b41724 := hb (x 5 3)
  have b41725 := hb (x 5 4)
  have b41726 := hb (x 5 8)
  have b41727 := hb (x 5 11)
  have b41728 := hb (x 6 2)
  have b41729 := hb (x 6 3)
  have b41730 := hb (x 6 7)
  have b41731 := hb (x 6 10)
  have b41732 := hb (x 6 11)
  have b41733 := hb (x 7 1)
  have b41734 := hb (x 7 2)
  have b41735 := hb (x 7 3)
  have b41736 := hb (x 7 5)
  have b41737 := hb (x 7 6)
  have b41738 := hb (x 7 7)
  have b41739 := hb (x 7 9)
  have b41740 := hb (x 7 10)
  have b41741 := hb (x 7 13)
  have b41742 := hb (x 8 2)
  have b41743 := hb (x 8 4)
  have b41744 := hb (x 8 5)
  have b41745 := hb (x 8 6)
  have b41746 := hb (x 8 7)
  have b41747 := hb (x 8 8)
  have b41748 := hb (x 8 9)
  have b41749 := hb (x 8 12)
  have b41750 := hb (x 8 13)
  have b41751 := hb (x 8 14)
  have b41752 := hb (x 9 4)
  have b41753 := hb (x 9 5)
  have b41754 := hb (x 9 6)
  have b41755 := hb (x 9 8)
  have b41756 := hb (x 9 12)
  have b41757 := hb (x 9 13)
  have b41758 := hb (x 10 3)
  have b41759 := hb (x 10 4)
  have b41760 := hb (x 10 5)
  have b41761 := hb (x 10 12)
  have b41762 := hb (x 11 2)
  have b41763 := hb (x 11 4)
  have b41764 := hb (x 11 11)
  have b41765 := hb (x 12 1)
  have b41766 := hb (x 12 10)
  have b41767 := hb (x 12 11)
  have b41768 := hb (x 13 9)
  have b41769 := hb (x 13 10)
  have b41770 := hb (x 14 8)
  have b41771 := hb (x 14 9)
  have b41772 := hb (x 15 8)
  have b41773 := hb (x 7 2 && x 7 6)
  have b41774 := hb (x 6 3 && x 6 7)
  have b41775 := hb (x 5 4 && x 5 8)
  have b41776 := hb (x 4 5 && x 4 9)
  have b41777 := hb (x 3 6 && x 3 10)
  have b41778 := hb (x 2 7 && x 2 11)
  have b41779 := hb (x 1 8 && x 1 12)
  have b41780 := hb (x 0 9 && x 0 13)
  have b41781 := hb (x 8 2 && x 8 6)
  have b41782 := hb (x 7 3 && x 7 7)
  have b41783 := hb (x 6 4 && x 6 8)
  have b41784 := hb (x 5 5 && x 5 9)
  have b41785 := hb (x 4 6 && x 4 10)
  have b41786 := hb (x 3 7 && x 3 11)
  have b41787 := hb (x 2 8 && x 2 12)
  have b41788 := hb (x 1 9 && x 1 13)
  have b41789 := hb (x 9 1 && x 9 6)
  have b41790 := hb (x 8 2 && x 8 7)
  have b41791 := hb (x 7 3 && x 7 8)
  have b41792 := hb (x 6 4 && x 6 9)
  have b41793 := hb (x 5 5 && x 5 10)
  have b41794 := hb (x 4 6 && x 4 11)
  have b41795 := hb (x 3 7 && x 3 12)
  have b41796 := hb (x 2 8 && x 2 13)
  have b41797 := hb (x 1 9 && x 1 14)
  have b41798 := hb (x 7 1 && x 7 8)
  have b41799 := hb (x 6 2 && x 6 9)
  have b41800 := hb (x 5 3 && x 5 10)
  have b41801 := hb (x 4 4 && x 4 11)
  have b41802 := hb (x 3 5 && x 3 12)
  have b41803 := hb (x 2 6 && x 2 13)
  have b41804 := hb (x 1 7 && x 1 14)
  have b41805 := hb (x 0 1 && x 0 10)
  have b41806 := hb (x (-1) 2 && x (-1) 11)
  have b41807 := hb (x (-2) 3 && x (-2) 12)
  have b41808 := hb (x (-3) 4 && x (-3) 13)
  have b41809 := hb (x (-4) 5 && x (-4) 14)
  have b41810 := hb (x 6 1 && x 6 10)
  have b41811 := hb (x 5 2 && x 5 11)
  have b41812 := hb (x 4 3 && x 4 12)
  have b41813 := hb (x 3 4 && x 3 13)
  have b41814 := hb (x 2 5 && x 2 14)
  have b41815 := hb (x 6 1 && x 6 11)
  have b41816 := hb (x 5 2 && x 5 12)
  have b41817 := hb (x 4 3 && x 4 13)
  have b41818 := hb (x 3 4 && x 3 14)
  have b41819 := hb (x 11 1 && x 11 11)
  have b41820 := hb (x 10 2 && x 10 12)
  have b41821 := hb (x 9 3 && x 9 13)
  have b41822 := hb (x 8 4 && x 8 14)
  have b41823 := hb (x 12 1 && x 12 11)
  have b41824 := hb (x 11 2 && x 11 12)
  have b41825 := hb (x 10 3 && x 10 13)
  have b41826 := hb (x 9 4 && x 9 14)
  have b41827 := hb (x 1 1 && x 1 12)
  have b41828 := hb (x 0 2 && x 0 13)
  have b41829 := hb (x (-1) 3 && x (-1) 14)
  linarith only [r41592, r41593, e41594, e41595, e41596, e41597, e41598, e41599, r41600, e41601, e41602, e41603, e41604, e41605, e41606, r41607, e41608, e41609, e41610, e41611, e41612, e41613, r41614, e41615, e41616, e41617, e41618, e41619, e41620, r41621, e41622, e41623, e41624, e41625, e41626, e41627, r41628, e41629, e41630, e41631, e41632, e41633, e41634, r41635, e41636, e41637, r41638, e41639, e41640, r41641, e41642, e41643, r41644, r41645, e41646, e41647, r41648, e41649, e41650, r41651, r41652, r41653, r41654, r41655, r41656, r41657, r41658, r41659, r41660, r41661, r41662, r41663, r41664, r41665, r41666, r41667, r41668, r41669, r41670, r41671, r41672, r41673, r41674, r41675, r41676, r41677, r41678, r41679, r41680, r41681, r41682, r41683, r41684, r41685, r41686, r41687, r41688, r41689, r41690, r41691, b41692, b41693, b41694, b41695, b41696, b41697, b41698, b41699, b41700, b41701, b41702, b41703, b41704, b41705, b41706, b41707, b41708, b41709, b41710, b41711, b41712, b41713, b41714, b41715, b41716, b41717, b41718, b41719, b41720, b41721, b41722, b41723, b41724, b41725, b41726, b41727, b41728, b41729, b41730, b41731, b41732, b41733, b41734, b41735, b41736, b41737, b41738, b41739, b41740, b41741, b41742, b41743, b41744, b41745, b41746, b41747, b41748, b41749, b41750, b41751, b41752, b41753, b41754, b41755, b41756, b41757, b41758, b41759, b41760, b41761, b41762, b41763, b41764, b41765, b41766, b41767, b41768, b41769, b41770, b41771, b41772, b41773, b41774, b41775, b41776, b41777, b41778, b41779, b41780, b41781, b41782, b41783, b41784, b41785, b41786, b41787, b41788, b41789, b41790, b41791, b41792, b41793, b41794, b41795, b41796, b41797, b41798, b41799, b41800, b41801, b41802, b41803, b41804, b41805, b41806, b41807, b41808, b41809, b41810, b41811, b41812, b41813, b41814, b41815, b41816, b41817, b41818, b41819, b41820, b41821, b41822, b41823, b41824, b41825, b41826, b41827, b41828, b41829, d41407, d41480, d41379, g4, g5, g6, g7, d41411, d41383, d41492, d41443, g10, g11, d41427, d41337, d41317, d41321, d41341, g12, d41391, g13, d41528, d41548, d41568, d41588, d41366, d41217, d41241, d41269, d41488, g14, g15, d41213, d41237, d41265, d41431, g16, g17, g18, d41484, d41403, d41423, g21, d41508, d41313, d41333, g24, d41358, g25, d41476]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0001 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x 0 5).toNat = 0)
    (g2 : (x 0 6).toNat = 0)
    (g3 : (x 0 7).toNat = 1)
    (g4 : (x 0 8).toNat = 0)
    (g5 : (x 0 10).toNat = 0)
    (g6 : (x 0 13).toNat = 0)
    (g7 : (x 1 6).toNat = 0)
    (g8 : (x 3 2).toNat = 0)
    (g9 : (x 3 4).toNat = 0)
    (g10 : (x 3 6).toNat = 0)
    (g11 : (x 3 10).toNat = 0)
    (g12 : (x 3 6 && x 3 10).toNat = 0)
    (g13 : (x 0 9 && x 0 13).toNat = 0)
    (g14 : (x 3 7 && x 3 12).toNat = 0)
    (g15 : (x 1 9 && x 1 14).toNat = 0)
    (g16 : (x 3 5 && x 3 12).toNat = 0)
    (g17 : (x 1 7 && x 1 14).toNat = 0)
    (g18 : (x 0 1 && x 0 10).toNat = 0)
    (g19 : (x 3 3 && x 3 12).toNat = 0)
    (g20 : (x 1 5 && x 1 14).toNat = 0)
    (g21 : (x 3 4 && x 3 13).toNat = 0)
    (g22 : (x 3 2 && x 3 12).toNat = 0)
    (g23 : (x 1 4 && x 1 14).toNat = 0)
    (g24 : (x 3 4 && x 3 14).toNat = 0)
    (g25 : (x 0 2 && x 0 13).toNat = 0)
    (g26 : (x 0 1 && x 0 14).toNat = 0)
    (g27 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a0001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27
