import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a1

Topic: combinatorics   Node: f7e1704a6c78

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 21 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a1_aux (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x 0 4).toNat = 1)
    (g2 : (x 0 10).toNat = 0)
    (g3 : (x 0 11).toNat = 0)
    (g4 : (x 1 2).toNat = 0)
    (g5 : (x 1 6).toNat = 0)
    (g6 : (x 1 10).toNat = 0)
    (g7 : (x 3 2).toNat = 0)
    (g8 : (x 3 4).toNat = 0)
    (g9 : (x 3 10).toNat = 0)
    (g10 : (x 1 2 && x 1 11).toNat = 0)
    (g11 : (x 0 3 && x 0 12).toNat = 0)
    (g12 : (x 0 1 && x 0 11).toNat = 0)
    (g13 : (x 1 2 && x 1 12).toNat = 0)
    (g14 : (x 0 3 && x 0 13).toNat = 0)
    (g15 : (x 3 2 && x 3 12).toNat = 0)
    (g16 : (x 1 4 && x 1 14).toNat = 0)
    (g17 : (x 1 2 && x 1 13).toNat = 0)
    (g18 : (x 0 3 && x 0 14).toNat = 0)
    (g19 : (x 0 1 && x 0 14).toNat = 0)
    (g20 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d49167 : (x 0 12).toNat = 1 := by
    have r49168 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
    have b49169 := hb (x 0 4)
    have b49170 := hb (x 0 12)
    clear * - r49168 b49169 b49170 g1
    omega
  have d49171 : (x (-1) 13).toNat = 0 := by
    have r49172 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
    have e49173 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e49174 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b49175 := hb (x (-3) 3)
    have b49176 := hb (x (-2) 2)
    have b49177 := hb (x (-1) 13)
    have b49178 := hb (x 0 12)
    clear * - r49172 e49173 e49174 b49175 b49176 b49177 b49178 d49167
    omega
  have d49179 : (x (-1) 4 && x (-1) 13).toNat = 0 := by
    have r49180 := hand2 (x (-1) 4) (x (-1) 13)
    have b49181 := hb (x (-1) 13)
    have b49182 := hb (x (-1) 4 && x (-1) 13)
    clear * - r49180 b49181 b49182 d49171
    omega
  have d49183 : (x (-1) 5).toNat = 0 := by
    have r49184 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b49185 := hb (x (-1) 5)
    have b49186 := hb (x (-1) 13)
    clear * - r49184 b49185 b49186 d49171
    omega
  have d49187 : (x (-2) 2).toNat = 0 := by
    have r49188 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
    have e49189 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e49190 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b49191 := hb (x (-3) 3)
    have b49192 := hb (x (-2) 2)
    have b49193 := hb (x (-1) 13)
    have b49194 := hb (x 0 12)
    clear * - r49188 e49189 e49190 b49191 b49192 b49193 b49194 d49167 d49171
    omega
  have d49195 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
    have r49196 := hand1 (x (-2) 2) (x (-2) 13)
    have b49197 := hb (x (-2) 2)
    have b49198 := hb (x (-2) 2 && x (-2) 13)
    clear * - r49196 b49197 b49198 d49187
    omega
  have d49199 : (x (-2) 2 && x (-2) 12).toNat = 0 := by
    have r49200 := hand1 (x (-2) 2) (x (-2) 12)
    have b49201 := hb (x (-2) 2)
    have b49202 := hb (x (-2) 2 && x (-2) 12)
    clear * - r49200 b49201 b49202 d49187
    omega
  have d49203 : (x (-2) 10).toNat = 0 := by
    have r49204 : (x (-2) 10).toNat ≤ (x (-2) 2).toNat := himp _ _ (hp10 (-2))
    have b49205 := hb (x (-2) 2)
    have b49206 := hb (x (-2) 10)
    clear * - r49204 b49205 b49206 d49187
    omega
  have d49207 : (x (-3) 3).toNat = 0 := by
    have r49208 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := hd12 0
    have e49209 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
    have e49210 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
    have b49211 := hb (x (-3) 3)
    have b49212 := hb (x (-2) 2)
    have b49213 := hb (x (-1) 13)
    have b49214 := hb (x 0 12)
    clear * - r49208 e49209 e49210 b49211 b49212 b49213 b49214 d49167 d49171 d49187
    omega
  have d49215 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
    have r49216 := hand1 (x (-3) 3) (x (-3) 14)
    have b49217 := hb (x (-3) 3)
    have b49218 := hb (x (-3) 3 && x (-3) 14)
    clear * - r49216 b49217 b49218 d49207
    omega
  have d49219 : (x (-3) 3 && x (-3) 13).toNat = 0 := by
    have r49220 := hand1 (x (-3) 3) (x (-3) 13)
    have b49221 := hb (x (-3) 3)
    have b49222 := hb (x (-3) 3 && x (-3) 13)
    clear * - r49220 b49221 b49222 d49207
    omega
  have d49223 : (x (-3) 11).toNat = 0 := by
    have r49224 : (x (-3) 11).toNat ≤ (x (-3) 3).toNat := himp _ _ (hp11 (-3))
    have b49225 := hb (x (-3) 3)
    have b49226 := hb (x (-3) 11)
    clear * - r49224 b49225 b49226 d49207
    omega
  have d49227 : (x 4 8).toNat = 0 := by
    have r49228 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
    have e49229 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e49230 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e49231 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e49232 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e49233 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e49234 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b49235 := hb (x (-3) 7)
    have b49236 := hb (x (-2) 6)
    have b49237 := hb (x (-1) 5)
    have b49238 := hb (x 0 4)
    have b49239 := hb (x 1 11)
    have b49240 := hb (x 2 10)
    have b49241 := hb (x 3 9)
    have b49242 := hb (x 4 8)
    clear * - r49228 e49229 e49230 e49231 e49232 e49233 e49234 b49235 b49236 b49237 b49238 b49239 b49240 b49241 b49242 g1 d49183
    omega
  have d49243 : (x 3 9).toNat = 0 := by
    have r49244 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
    have e49245 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e49246 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e49247 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e49248 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e49249 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e49250 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b49251 := hb (x (-3) 7)
    have b49252 := hb (x (-2) 6)
    have b49253 := hb (x (-1) 5)
    have b49254 := hb (x 0 4)
    have b49255 := hb (x 1 11)
    have b49256 := hb (x 2 10)
    have b49257 := hb (x 3 9)
    have b49258 := hb (x 4 8)
    clear * - r49244 e49245 e49246 e49247 e49248 e49249 e49250 b49251 b49252 b49253 b49254 b49255 b49256 b49257 b49258 d49227 g1 d49183
    omega
  have d49259 : (x 2 10).toNat = 0 := by
    have r49260 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := hd8 4
    have e49261 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e49262 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e49263 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e49264 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e49265 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e49266 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b49267 := hb (x (-3) 7)
    have b49268 := hb (x (-2) 6)
    have b49269 := hb (x (-1) 5)
    have b49270 := hb (x 0 4)
    have b49271 := hb (x 1 11)
    have b49272 := hb (x 2 10)
    have b49273 := hb (x 3 9)
    have b49274 := hb (x 4 8)
    clear * - r49260 e49261 e49262 e49263 e49264 e49265 e49266 b49267 b49268 b49269 b49270 b49271 b49272 b49273 b49274 d49227 d49243 g1 d49183
    omega
  have d49275 : (x 2 1 && x 2 10).toNat = 0 := by
    have r49276 := hand2 (x 2 1) (x 2 10)
    have b49277 := hb (x 2 10)
    have b49278 := hb (x 2 1 && x 2 10)
    clear * - r49276 b49277 b49278 d49259
    omega
  cases h49279 : x 0 5
  · have f49280 : (x 0 5).toNat = 0 := by rw [h49279]; rfl
    cases h49281 : x 0 7
    · have f49282 : (x 0 7).toNat = 0 := by rw [h49281]; rfl
      cases h49283 : x 0 8
      · have f49284 : (x 0 8).toNat = 0 := by rw [h49283]; rfl
        cases h49285 : x 0 9
        · have f49286 : (x 0 9).toNat = 0 := by rw [h49285]; rfl
          cases h49287 : x 0 13
          · have f49288 : (x 0 13).toNat = 0 := by rw [h49287]; rfl
            have d49289 : (x (-1) 1 && x (-1) 14).toNat = 1 := by
              have r49290 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := hcov13 0
              have b49291 := hb (x (-2) 2)
              have b49292 := hb (x 0 13)
              have b49293 := hb (x (-1) 1 && x (-1) 14)
              clear * - r49290 b49291 b49292 b49293 f49288 d49187
              omega
            have d49294 : (x (-1) 14).toNat = 1 := by
              have r49295 := hand2 (x (-1) 1) (x (-1) 14)
              have b49296 := hb (x (-1) 14)
              have b49297 := hb (x (-1) 1 && x (-1) 14)
              clear * - r49295 b49296 b49297 d49289
              omega
            have d49298 : (x (-2) 1).toNat = 0 := by
              have r49299 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
              have b49300 := hb (x (-2) 1)
              have b49301 := hb (x (-1) 14)
              clear * - r49299 b49300 b49301 d49294
              omega
            have d49302 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
              have r49303 := hand1 (x (-2) 1) (x (-2) 14)
              have b49304 := hb (x (-2) 1)
              have b49305 := hb (x (-2) 1 && x (-2) 14)
              clear * - r49303 b49304 b49305 d49298
              omega
            have d49306 : (x (-2) 13).toNat = 0 := by
              have r49307 : (x (-2) 13).toNat ≤ (x (-2) 1).toNat := himp _ _ (hp13 (-2))
              have b49308 := hb (x (-2) 1)
              have b49309 := hb (x (-2) 13)
              clear * - r49307 b49308 b49309 d49298
              omega
            have d49310 : (x (-2) 5).toNat = 0 := by
              have r49311 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
              have b49312 := hb (x (-2) 5)
              have b49313 := hb (x (-2) 13)
              clear * - r49311 b49312 b49313 d49306
              omega
            have d49314 : (x (-3) 2).toNat = 1 := by
              have r49315 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
              have b49316 := hb (x (-3) 2)
              have b49317 := hb (x (-1) 13)
              have b49318 := hb (x (-2) 1 && x (-2) 14)
              clear * - r49315 b49316 b49317 b49318 d49171 d49302
              omega
            have d49319 : (x (-3) 14).toNat = 1 := by
              have r49320 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
              have b49321 := hb (x (-3) 2)
              have b49322 := hb (x (-3) 14)
              clear * - r49320 b49321 b49322 d49314
              omega
            have d49323 : (x (-4) 1).toNat = 0 := by
              have r49324 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
              have b49325 := hb (x (-4) 1)
              have b49326 := hb (x (-3) 14)
              clear * - r49324 b49325 b49326 d49319
              omega
            have d49327 : (x (-4) 13).toNat = 0 := by
              have r49328 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
              have b49329 := hb (x (-4) 1)
              have b49330 := hb (x (-4) 13)
              clear * - r49328 b49329 b49330 d49323
              omega
            have d49331 : (x (-1) 12).toNat = 0 := by
              have r49332 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
              have e49333 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
              have e49334 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
              have b49335 := hb (x (-4) 3)
              have b49336 := hb (x (-3) 2)
              have b49337 := hb (x (-2) 13)
              have b49338 := hb (x (-1) 12)
              clear * - r49332 e49333 e49334 b49335 b49336 b49337 b49338 d49306 d49314
              omega
            have d49339 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
              have r49340 := hand2 (x (-1) 1) (x (-1) 12)
              have b49341 := hb (x (-1) 12)
              have b49342 := hb (x (-1) 1 && x (-1) 12)
              clear * - r49340 b49341 b49342 d49331
              omega
            have d49343 : (x (-1) 4).toNat = 0 := by
              have r49344 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
              have b49345 := hb (x (-1) 4)
              have b49346 := hb (x (-1) 12)
              clear * - r49344 b49345 b49346 d49331
              omega
            have d49347 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
              have r49348 := hand1 (x (-1) 4) (x (-1) 14)
              have b49349 := hb (x (-1) 4)
              have b49350 := hb (x (-1) 4 && x (-1) 14)
              clear * - r49348 b49349 b49350 d49343
              omega
            have d49351 : (x (-4) 4).toNat = 1 := by
              have r49352 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
              have b49353 := hb (x (-4) 4)
              have b49354 := hb (x 0 11)
              have b49355 := hb (x (-1) 1 && x (-1) 12)
              have b49356 := hb (x (-2) 2 && x (-2) 13)
              have b49357 := hb (x (-3) 3 && x (-3) 14)
              clear * - r49352 b49353 b49354 b49355 b49356 b49357 g3 d49339 d49195 d49215
              omega
            have d49358 : (x (-4) 12).toNat = 1 := by
              have r49359 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
              have b49360 := hb (x (-4) 4)
              have b49361 := hb (x (-4) 12)
              clear * - r49359 b49360 b49361 d49351
              omega
            have d49362 : (x (-5) 13).toNat = 0 := by
              have r49363 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
              have e49364 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e49365 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b49366 := hb (x (-7) 3)
              have b49367 := hb (x (-6) 2)
              have b49368 := hb (x (-5) 13)
              have b49369 := hb (x (-4) 12)
              clear * - r49363 e49364 e49365 b49366 b49367 b49368 b49369 d49358
              omega
            have d49370 : (x (-5) 5).toNat = 0 := by
              have r49371 : (x (-5) 5).toNat ≤ (x (-5) 13).toNat := himp _ _ (hp5 (-5))
              have b49372 := hb (x (-5) 5)
              have b49373 := hb (x (-5) 13)
              clear * - r49371 b49372 b49373 d49362
              omega
            have d49374 : (x (-6) 2).toNat = 0 := by
              have r49375 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
              have e49376 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
              have e49377 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
              have b49378 := hb (x (-7) 3)
              have b49379 := hb (x (-6) 2)
              have b49380 := hb (x (-5) 13)
              have b49381 := hb (x (-4) 12)
              clear * - r49375 e49376 e49377 b49378 b49379 b49380 b49381 d49358 d49362
              omega
            have d49382 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
              have r49383 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := hcov13 (-4)
              have b49384 := hb (x (-6) 2)
              have b49385 := hb (x (-4) 13)
              have b49386 := hb (x (-5) 1 && x (-5) 14)
              clear * - r49383 b49384 b49385 b49386 d49327 d49374
              omega
            have d49387 : (x (-5) 1).toNat = 1 := by
              have r49388 := hand1 (x (-5) 1) (x (-5) 14)
              have b49389 := hb (x (-5) 1)
              have b49390 := hb (x (-5) 1 && x (-5) 14)
              clear * - r49388 b49389 b49390 d49382
              omega
            have d49391 : (x (-4) 14).toNat = 0 := by
              have r49392 : (x (-4) 14).toNat + (x (-5) 1).toNat = 1 := hd14 (-4)
              have b49393 := hb (x (-5) 1)
              have b49394 := hb (x (-4) 14)
              clear * - r49392 b49393 b49394 d49387
              omega
            have d49395 : (x (-4) 4 && x (-4) 14).toNat = 0 := by
              have r49396 := hand2 (x (-4) 4) (x (-4) 14)
              have b49397 := hb (x (-4) 14)
              have b49398 := hb (x (-4) 4 && x (-4) 14)
              clear * - r49396 b49397 b49398 d49391
              omega
            have d49399 : (x 2 1 && x 2 11).toNat = 1 := by
              have r49400 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := hcov10 3
              have b49401 := hb (x (-2) 5)
              have b49402 := hb (x 3 10)
              have b49403 := hb (x 2 1 && x 2 11)
              have b49404 := hb (x 1 2 && x 1 12)
              have b49405 := hb (x 0 3 && x 0 13)
              have b49406 := hb (x (-1) 4 && x (-1) 14)
              clear * - r49400 b49401 b49402 b49403 b49404 b49405 b49406 g9 g13 g14 d49347 d49310
              omega
            have d49407 : (x 2 11).toNat = 1 := by
              have r49408 := hand2 (x 2 1) (x 2 11)
              have b49409 := hb (x 2 11)
              have b49410 := hb (x 2 1 && x 2 11)
              clear * - r49408 b49409 b49410 d49399
              omega
            have d49411 : (x 2 3).toNat = 1 := by
              have r49412 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
              have b49413 := hb (x 2 3)
              have b49414 := hb (x 2 11)
              clear * - r49412 b49413 b49414 d49407
              omega
            have d49415 : (x 5 12).toNat = 0 := by
              have r49416 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
              have e49417 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e49418 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b49419 := hb (x 2 3)
              have b49420 := hb (x 3 2)
              have b49421 := hb (x 4 13)
              have b49422 := hb (x 5 12)
              clear * - r49416 e49417 e49418 b49419 b49420 b49421 b49422 g7 d49411
              omega
            have d49423 : (x 4 13).toNat = 0 := by
              have r49424 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
              have e49425 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
              have e49426 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
              have b49427 := hb (x 2 3)
              have b49428 := hb (x 3 2)
              have b49429 := hb (x 4 13)
              have b49430 := hb (x 5 12)
              clear * - r49424 e49425 e49426 b49427 b49428 b49429 b49430 d49415 g7 d49411
              omega
            have d49431 : (x 2 2).toNat = 1 := by
              have r49432 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
              have b49433 := hb (x 2 2)
              have b49434 := hb (x 4 13)
              have b49435 := hb (x 3 1 && x 3 14)
              clear * - r49432 b49433 b49434 b49435 d49423 g20
              omega
            have d49436 : (x 2 14).toNat = 1 := by
              have r49437 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
              have b49438 := hb (x 2 2)
              have b49439 := hb (x 2 14)
              clear * - r49437 b49438 b49439 d49431
              omega
            have d49440 : (x 1 1).toNat = 0 := by
              have r49441 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
              have b49442 := hb (x 1 1)
              have b49443 := hb (x 2 14)
              clear * - r49441 b49442 b49443 d49436
              omega
            have d49444 : (x 1 13).toNat = 0 := by
              have r49445 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
              have b49446 := hb (x 1 1)
              have b49447 := hb (x 1 13)
              clear * - r49445 b49446 b49447 d49440
              omega
            have d49448 : (x 4 12).toNat = 0 := by
              have r49449 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
              have e49450 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e49451 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b49452 := hb (x 1 3)
              have b49453 := hb (x 2 2)
              have b49454 := hb (x 3 13)
              have b49455 := hb (x 4 12)
              clear * - r49449 e49450 e49451 b49452 b49453 b49454 b49455 d49431
              omega
            have d49456 : (x 4 4).toNat = 0 := by
              have r49457 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
              have b49458 := hb (x 4 4)
              have b49459 := hb (x 4 12)
              clear * - r49457 b49458 b49459 d49448
              omega
            have d49460 : (x 4 4 && x 4 14).toNat = 0 := by
              have r49461 := hand1 (x 4 4) (x 4 14)
              have b49462 := hb (x 4 4)
              have b49463 := hb (x 4 4 && x 4 14)
              clear * - r49461 b49462 b49463 d49456
              omega
            have d49464 : (x 3 13).toNat = 0 := by
              have r49465 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
              have e49466 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e49467 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b49468 := hb (x 1 3)
              have b49469 := hb (x 2 2)
              have b49470 := hb (x 3 13)
              have b49471 := hb (x 4 12)
              clear * - r49465 e49466 e49467 b49468 b49469 b49470 b49471 d49448 d49431
              omega
            have d49472 : (x 3 5).toNat = 0 := by
              have r49473 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
              have b49474 := hb (x 3 5)
              have b49475 := hb (x 3 13)
              clear * - r49473 b49474 b49475 d49464
              omega
            have d49476 : (x (-1) 1 && x (-1) 11).toNat = 1 := by
              have r49477 : 1 ≤ (x 0 10).toNat + (x (-1) 1 && x (-1) 11).toNat + (x (-2) 2 && x (-2) 12).toNat + (x (-3) 3 && x (-3) 13).toNat + (x (-4) 4 && x (-4) 14).toNat + (x (-5) 5).toNat := hcov10 0
              have b49478 := hb (x (-5) 5)
              have b49479 := hb (x 0 10)
              have b49480 := hb (x (-1) 1 && x (-1) 11)
              have b49481 := hb (x (-2) 2 && x (-2) 12)
              have b49482 := hb (x (-3) 3 && x (-3) 13)
              have b49483 := hb (x (-4) 4 && x (-4) 14)
              clear * - r49477 b49478 b49479 b49480 b49481 b49482 b49483 g2 d49199 d49219 d49395 d49370
              omega
            have d49484 : (x (-1) 11).toNat = 1 := by
              have r49485 := hand2 (x (-1) 1) (x (-1) 11)
              have b49486 := hb (x (-1) 11)
              have b49487 := hb (x (-1) 1 && x (-1) 11)
              clear * - r49485 b49486 b49487 d49476
              omega
            have d49488 : (x (-1) 3).toNat = 1 := by
              have r49489 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
              have b49490 := hb (x (-1) 3)
              have b49491 := hb (x (-1) 11)
              clear * - r49489 b49490 b49491 d49484
              omega
            have d49492 : (x 2 12).toNat = 0 := by
              have r49493 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := hd12 2
              have e49494 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
              have e49495 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
              have b49496 := hb (x (-1) 3)
              have b49497 := hb (x 0 2)
              have b49498 := hb (x 1 13)
              have b49499 := hb (x 2 12)
              clear * - r49493 e49494 e49495 b49496 b49497 b49498 b49499 d49444 g0 d49488
              omega
            have d49500 : (x 2 1 && x 2 12).toNat = 0 := by
              have r49501 := hand2 (x 2 1) (x 2 12)
              have b49502 := hb (x 2 12)
              have b49503 := hb (x 2 1 && x 2 12)
              clear * - r49501 b49502 b49503 d49492
              omega
            have d49504 : (x 3 11).toNat = 1 := by
              have r49505 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := hcov11 3
              have b49506 := hb (x (-1) 4)
              have b49507 := hb (x 3 11)
              have b49508 := hb (x 2 1 && x 2 12)
              have b49509 := hb (x 1 2 && x 1 13)
              have b49510 := hb (x 0 3 && x 0 14)
              clear * - r49505 b49506 b49507 b49508 b49509 b49510 d49500 g17 g18 d49343
              omega
            have d49511 : (x 3 3).toNat = 1 := by
              have r49512 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
              have b49513 := hb (x 3 3)
              have b49514 := hb (x 3 11)
              clear * - r49512 b49513 b49514 d49504
              omega
            have d49515 : (x 6 12).toNat = 0 := by
              have r49516 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
              have e49517 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e49518 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b49519 := hb (x 3 3)
              have b49520 := hb (x 4 2)
              have b49521 := hb (x 5 13)
              have b49522 := hb (x 6 12)
              clear * - r49516 e49517 e49518 b49519 b49520 b49521 b49522 d49511
              omega
            have d49523 : (x 6 1 && x 6 12).toNat = 0 := by
              have r49524 := hand2 (x 6 1) (x 6 12)
              have b49525 := hb (x 6 12)
              have b49526 := hb (x 6 1 && x 6 12)
              clear * - r49524 b49525 b49526 d49515
              omega
            have d49527 : (x 6 2 && x 6 12).toNat = 0 := by
              have r49528 := hand2 (x 6 2) (x 6 12)
              have b49529 := hb (x 6 12)
              have b49530 := hb (x 6 2 && x 6 12)
              clear * - r49528 b49529 b49530 d49515
              omega
            have d49531 : (x 5 13).toNat = 0 := by
              have r49532 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
              have e49533 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e49534 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b49535 := hb (x 3 3)
              have b49536 := hb (x 4 2)
              have b49537 := hb (x 5 13)
              have b49538 := hb (x 6 12)
              clear * - r49532 e49533 e49534 b49535 b49536 b49537 b49538 d49515 d49511
              omega
            have d49539 : (x 5 2 && x 5 13).toNat = 0 := by
              have r49540 := hand2 (x 5 2) (x 5 13)
              have b49541 := hb (x 5 13)
              have b49542 := hb (x 5 2 && x 5 13)
              clear * - r49540 b49541 b49542 d49531
              omega
            have d49543 : (x 5 3 && x 5 13).toNat = 0 := by
              have r49544 := hand2 (x 5 3) (x 5 13)
              have b49545 := hb (x 5 13)
              have b49546 := hb (x 5 3 && x 5 13)
              clear * - r49544 b49545 b49546 d49531
              omega
            have d49547 : (x 4 1 && x 4 14).toNat = 1 := by
              have r49548 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
              have b49549 := hb (x 3 2)
              have b49550 := hb (x 5 13)
              have b49551 := hb (x 4 1 && x 4 14)
              clear * - r49548 b49549 b49550 b49551 d49531 g7
              omega
            have d49552 : (x 4 1).toNat = 1 := by
              have r49553 := hand1 (x 4 1) (x 4 14)
              have b49554 := hb (x 4 1)
              have b49555 := hb (x 4 1 && x 4 14)
              clear * - r49553 b49554 b49555 d49547
              omega
            have d49556 : (x 5 14).toNat = 0 := by
              have r49557 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
              have b49558 := hb (x 4 1)
              have b49559 := hb (x 5 14)
              clear * - r49557 b49558 b49559 d49552
              omega
            have d49560 : (x 5 1 && x 5 14).toNat = 0 := by
              have r49561 := hand2 (x 5 1) (x 5 14)
              have b49562 := hb (x 5 14)
              have b49563 := hb (x 5 1 && x 5 14)
              clear * - r49561 b49562 b49563 d49556
              omega
            have d49564 : (x 5 2).toNat = 0 := by
              have r49565 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
              have b49566 := hb (x 5 2)
              have b49567 := hb (x 5 14)
              clear * - r49565 b49566 b49567 d49556
              omega
            have d49568 : (x 4 2).toNat = 0 := by
              have r49569 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
              have e49570 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e49571 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b49572 := hb (x 3 3)
              have b49573 := hb (x 4 2)
              have b49574 := hb (x 5 13)
              have b49575 := hb (x 6 12)
              clear * - r49569 e49570 e49571 b49572 b49573 b49574 b49575 d49515 d49531 d49511
              omega
            have d49576 : (x 6 13).toNat = 1 := by
              have r49577 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
              have b49578 := hb (x 4 2)
              have b49579 := hb (x 6 13)
              have b49580 := hb (x 5 1 && x 5 14)
              clear * - r49577 b49578 b49579 b49580 d49560 d49568
              omega
            have d49581 : (x 6 1).toNat = 1 := by
              have r49582 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
              have b49583 := hb (x 6 1)
              have b49584 := hb (x 6 13)
              clear * - r49582 b49583 b49584 d49576
              omega
            have d49585 : (x 7 14).toNat = 0 := by
              have r49586 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
              have b49587 := hb (x 6 1)
              have b49588 := hb (x 7 14)
              clear * - r49586 b49587 b49588 d49581
              omega
            have d49589 : (x 7 2).toNat = 0 := by
              have r49590 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
              have b49591 := hb (x 7 2)
              have b49592 := hb (x 7 14)
              clear * - r49590 b49591 b49592 d49585
              omega
            have d49593 : (x 7 12).toNat = 0 := by
              have r49594 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
              have e49595 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e49596 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have b49597 := hb (x 4 3)
              have b49598 := hb (x 5 2)
              have b49599 := hb (x 6 13)
              have b49600 := hb (x 7 12)
              clear * - r49594 e49595 e49596 b49597 b49598 b49599 b49600 d49576 d49564
              omega
            have d49601 : (x 4 3).toNat = 0 := by
              have r49602 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
              have e49603 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e49604 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have b49605 := hb (x 4 3)
              have b49606 := hb (x 5 2)
              have b49607 := hb (x 6 13)
              have b49608 := hb (x 7 12)
              clear * - r49602 e49603 e49604 b49605 b49606 b49607 b49608 d49593 d49576 d49564
              omega
            have d49609 : (x 4 3 && x 4 14).toNat = 0 := by
              have r49610 := hand1 (x 4 3) (x 4 14)
              have b49611 := hb (x 4 3)
              have b49612 := hb (x 4 3 && x 4 14)
              clear * - r49610 b49611 b49612 d49601
              omega
            have d49613 : (x 7 11).toNat = 1 := by
              have r49614 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := hcov11 7
              have b49615 := hb (x 3 4)
              have b49616 := hb (x 7 11)
              have b49617 := hb (x 6 1 && x 6 12)
              have b49618 := hb (x 5 2 && x 5 13)
              have b49619 := hb (x 4 3 && x 4 14)
              clear * - r49614 b49615 b49616 b49617 b49618 b49619 d49523 d49539 d49609 g8
              omega
            have d49620 : (x 7 3).toNat = 1 := by
              have r49621 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
              have b49622 := hb (x 7 3)
              have b49623 := hb (x 7 11)
              clear * - r49621 b49622 b49623 d49613
              omega
            have d49624 : (x 10 12).toNat = 0 := by
              have r49625 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
              have e49626 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
              have e49627 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
              have b49628 := hb (x 7 3)
              have b49629 := hb (x 8 2)
              have b49630 := hb (x 9 13)
              have b49631 := hb (x 10 12)
              clear * - r49625 e49626 e49627 b49628 b49629 b49630 b49631 d49620
              omega
            have d49632 : (x 9 13).toNat = 0 := by
              have r49633 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
              have e49634 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
              have e49635 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
              have b49636 := hb (x 7 3)
              have b49637 := hb (x 8 2)
              have b49638 := hb (x 9 13)
              have b49639 := hb (x 10 12)
              clear * - r49633 e49634 e49635 b49636 b49637 b49638 b49639 d49624 d49620
              omega
            have d49640 : (x 8 1 && x 8 14).toNat = 1 := by
              have r49641 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
              have b49642 := hb (x 7 2)
              have b49643 := hb (x 9 13)
              have b49644 := hb (x 8 1 && x 8 14)
              clear * - r49641 b49642 b49643 b49644 d49632 d49589
              omega
            have d49645 : (x 8 14).toNat = 1 := by
              have r49646 := hand2 (x 8 1) (x 8 14)
              have b49647 := hb (x 8 14)
              have b49648 := hb (x 8 1 && x 8 14)
              clear * - r49646 b49647 b49648 d49640
              omega
            have d49649 : (x 7 1).toNat = 0 := by
              have r49650 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
              have b49651 := hb (x 7 1)
              have b49652 := hb (x 8 14)
              clear * - r49650 b49651 b49652 d49645
              omega
            have d49653 : (x 7 1 && x 7 11).toNat = 0 := by
              have r49654 := hand1 (x 7 1) (x 7 11)
              have b49655 := hb (x 7 1)
              have b49656 := hb (x 7 1 && x 7 11)
              clear * - r49654 b49655 b49656 d49649
              omega
            have d49657 : (x 8 10).toNat = 1 := by
              have r49658 : 1 ≤ (x 8 10).toNat + (x 7 1 && x 7 11).toNat + (x 6 2 && x 6 12).toNat + (x 5 3 && x 5 13).toNat + (x 4 4 && x 4 14).toNat + (x 3 5).toNat := hcov10 8
              have b49659 := hb (x 3 5)
              have b49660 := hb (x 8 10)
              have b49661 := hb (x 7 1 && x 7 11)
              have b49662 := hb (x 6 2 && x 6 12)
              have b49663 := hb (x 5 3 && x 5 13)
              have b49664 := hb (x 4 4 && x 4 14)
              clear * - r49658 b49659 b49660 b49661 b49662 b49663 b49664 d49653 d49527 d49543 d49460 d49472
              omega
            have d49665 : (x 8 2).toNat = 1 := by
              have r49666 : (x 8 10).toNat ≤ (x 8 2).toNat := himp _ _ (hp10 8)
              have b49667 := hb (x 8 2)
              have b49668 := hb (x 8 10)
              clear * - r49666 b49667 b49668 d49657
              omega
            have r49669 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
            have e49670 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
            have e49671 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
            have b49672 := hb (x 7 3)
            have b49673 := hb (x 8 2)
            have b49674 := hb (x 9 13)
            have b49675 := hb (x 10 12)
            linarith only [r49669, e49670, e49671, b49672, b49673, b49674, b49675, d49624, d49632, d49665, d49620]
          · have f49676 : (x 0 13).toNat = 1 := by rw [h49287]; rfl
            have d49677 : (x 1 12).toNat = 0 := by
              have r49678 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
              have e49679 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
              have e49680 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
              have b49681 := hb (x (-2) 3)
              have b49682 := hb (x (-1) 2)
              have b49683 := hb (x 0 13)
              have b49684 := hb (x 1 12)
              clear * - r49678 e49679 e49680 b49681 b49682 b49683 b49684 f49676
              omega
            have d49685 : (x (-1) 2).toNat = 0 := by
              have r49686 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
              have e49687 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
              have e49688 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
              have b49689 := hb (x (-2) 3)
              have b49690 := hb (x (-1) 2)
              have b49691 := hb (x 0 13)
              have b49692 := hb (x 1 12)
              clear * - r49686 e49687 e49688 b49689 b49690 b49691 b49692 d49677 f49676
              omega
            have d49693 : (x 1 13).toNat = 1 := by
              have r49694 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
              have b49695 := hb (x (-1) 2)
              have b49696 := hb (x 1 13)
              have b49697 := hb (x 0 1 && x 0 14)
              clear * - r49694 b49695 b49696 b49697 g19 d49685
              omega
            have d49698 : (x 1 1).toNat = 1 := by
              have r49699 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
              have b49700 := hb (x 1 1)
              have b49701 := hb (x 1 13)
              clear * - r49699 b49700 b49701 d49693
              omega
            have d49702 : (x 2 14).toNat = 0 := by
              have r49703 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
              have b49704 := hb (x 1 1)
              have b49705 := hb (x 2 14)
              clear * - r49703 b49704 b49705 d49698
              omega
            have d49706 : (x 2 1 && x 2 14).toNat = 0 := by
              have r49707 := hand2 (x 2 1) (x 2 14)
              have b49708 := hb (x 2 14)
              have b49709 := hb (x 2 1 && x 2 14)
              clear * - r49707 b49708 b49709 d49702
              omega
            have d49710 : (x 3 13).toNat = 1 := by
              have r49711 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
              have b49712 := hb (x 1 2)
              have b49713 := hb (x 3 13)
              have b49714 := hb (x 2 1 && x 2 14)
              clear * - r49711 b49712 b49713 b49714 d49706 g4
              omega
            have d49715 : (x 3 1).toNat = 1 := by
              have r49716 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
              have b49717 := hb (x 3 1)
              have b49718 := hb (x 3 13)
              clear * - r49716 b49717 b49718 d49710
              omega
            have d49719 : (x 4 14).toNat = 0 := by
              have r49720 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
              have b49721 := hb (x 3 1)
              have b49722 := hb (x 4 14)
              clear * - r49720 b49721 b49722 d49715
              omega
            have d49723 : (x 4 1 && x 4 14).toNat = 0 := by
              have r49724 := hand2 (x 4 1) (x 4 14)
              have b49725 := hb (x 4 14)
              have b49726 := hb (x 4 1 && x 4 14)
              clear * - r49724 b49725 b49726 d49719
              omega
            have d49727 : (x 5 13).toNat = 1 := by
              have r49728 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
              have b49729 := hb (x 3 2)
              have b49730 := hb (x 5 13)
              have b49731 := hb (x 4 1 && x 4 14)
              clear * - r49728 b49729 b49730 b49731 d49723 g7
              omega
            have d49732 : (x 5 1).toNat = 1 := by
              have r49733 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
              have b49734 := hb (x 5 1)
              have b49735 := hb (x 5 13)
              clear * - r49733 b49734 b49735 d49727
              omega
            have d49736 : (x 6 14).toNat = 0 := by
              have r49737 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
              have b49738 := hb (x 5 1)
              have b49739 := hb (x 6 14)
              clear * - r49737 b49738 b49739 d49732
              omega
            have d49740 : (x 6 1 && x 6 14).toNat = 0 := by
              have r49741 := hand2 (x 6 1) (x 6 14)
              have b49742 := hb (x 6 14)
              have b49743 := hb (x 6 1 && x 6 14)
              clear * - r49741 b49742 b49743 d49736
              omega
            have d49744 : (x 6 2).toNat = 0 := by
              have r49745 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
              have b49746 := hb (x 6 2)
              have b49747 := hb (x 6 14)
              clear * - r49745 b49746 b49747 d49736
              omega
            have d49748 : (x 6 12).toNat = 0 := by
              have r49749 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
              have e49750 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e49751 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b49752 := hb (x 3 3)
              have b49753 := hb (x 4 2)
              have b49754 := hb (x 5 13)
              have b49755 := hb (x 6 12)
              clear * - r49749 e49750 e49751 b49752 b49753 b49754 b49755 d49727
              omega
            have d49756 : (x 4 2).toNat = 0 := by
              have r49757 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
              have e49758 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e49759 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have b49760 := hb (x 3 3)
              have b49761 := hb (x 4 2)
              have b49762 := hb (x 5 13)
              have b49763 := hb (x 6 12)
              clear * - r49757 e49758 e49759 b49760 b49761 b49762 b49763 d49748 d49727
              omega
            have d49764 : (x 4 12).toNat = 0 := by
              have r49765 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
              have e49766 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e49767 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b49768 := hb (x 1 3)
              have b49769 := hb (x 2 2)
              have b49770 := hb (x 3 13)
              have b49771 := hb (x 4 12)
              clear * - r49765 e49766 e49767 b49768 b49769 b49770 b49771 d49710
              omega
            have d49772 : (x 2 2).toNat = 0 := by
              have r49773 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
              have e49774 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
              have e49775 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
              have b49776 := hb (x 1 3)
              have b49777 := hb (x 2 2)
              have b49778 := hb (x 3 13)
              have b49779 := hb (x 4 12)
              clear * - r49773 e49774 e49775 b49776 b49777 b49778 b49779 d49764 d49710
              omega
            have d49780 : (x 4 13).toNat = 1 := by
              have r49781 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
              have b49782 := hb (x 2 2)
              have b49783 := hb (x 4 13)
              have b49784 := hb (x 3 1 && x 3 14)
              clear * - r49781 b49782 b49783 b49784 g20 d49772
              omega
            have d49785 : (x 4 1).toNat = 1 := by
              have r49786 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
              have b49787 := hb (x 4 1)
              have b49788 := hb (x 4 13)
              clear * - r49786 b49787 b49788 d49780
              omega
            have d49789 : (x 5 14).toNat = 0 := by
              have r49790 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
              have b49791 := hb (x 4 1)
              have b49792 := hb (x 5 14)
              clear * - r49790 b49791 b49792 d49785
              omega
            have d49793 : (x 5 1 && x 5 14).toNat = 0 := by
              have r49794 := hand2 (x 5 1) (x 5 14)
              have b49795 := hb (x 5 14)
              have b49796 := hb (x 5 1 && x 5 14)
              clear * - r49794 b49795 b49796 d49789
              omega
            have d49797 : (x 6 13).toNat = 1 := by
              have r49798 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
              have b49799 := hb (x 4 2)
              have b49800 := hb (x 6 13)
              have b49801 := hb (x 5 1 && x 5 14)
              clear * - r49798 b49799 b49800 b49801 d49793 d49756
              omega
            have d49802 : (x 6 1).toNat = 1 := by
              have r49803 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
              have b49804 := hb (x 6 1)
              have b49805 := hb (x 6 13)
              clear * - r49803 b49804 b49805 d49797
              omega
            have d49806 : (x 7 14).toNat = 0 := by
              have r49807 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
              have b49808 := hb (x 6 1)
              have b49809 := hb (x 7 14)
              clear * - r49807 b49808 b49809 d49802
              omega
            have d49810 : (x 7 1 && x 7 14).toNat = 0 := by
              have r49811 := hand2 (x 7 1) (x 7 14)
              have b49812 := hb (x 7 14)
              have b49813 := hb (x 7 1 && x 7 14)
              clear * - r49811 b49812 b49813 d49806
              omega
            have d49814 : (x 8 13).toNat = 1 := by
              have r49815 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
              have b49816 := hb (x 6 2)
              have b49817 := hb (x 8 13)
              have b49818 := hb (x 7 1 && x 7 14)
              clear * - r49815 b49816 b49817 b49818 d49810 d49744
              omega
            have d49819 : (x 8 1).toNat = 1 := by
              have r49820 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
              have b49821 := hb (x 8 1)
              have b49822 := hb (x 8 13)
              clear * - r49820 b49821 b49822 d49814
              omega
            have d49823 : (x 9 14).toNat = 0 := by
              have r49824 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
              have b49825 := hb (x 8 1)
              have b49826 := hb (x 9 14)
              clear * - r49824 b49825 b49826 d49819
              omega
            have d49827 : (x 9 1 && x 9 14).toNat = 0 := by
              have r49828 := hand2 (x 9 1) (x 9 14)
              have b49829 := hb (x 9 14)
              have b49830 := hb (x 9 1 && x 9 14)
              clear * - r49828 b49829 b49830 d49823
              omega
            have d49831 : (x 9 2).toNat = 0 := by
              have r49832 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
              have b49833 := hb (x 9 2)
              have b49834 := hb (x 9 14)
              clear * - r49832 b49833 b49834 d49823
              omega
            have d49835 : (x 9 12).toNat = 0 := by
              have r49836 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
              have e49837 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e49838 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b49839 := hb (x 6 3)
              have b49840 := hb (x 7 2)
              have b49841 := hb (x 8 13)
              have b49842 := hb (x 9 12)
              clear * - r49836 e49837 e49838 b49839 b49840 b49841 b49842 d49814
              omega
            have d49843 : (x 7 2).toNat = 0 := by
              have r49844 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
              have e49845 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
              have e49846 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
              have b49847 := hb (x 6 3)
              have b49848 := hb (x 7 2)
              have b49849 := hb (x 8 13)
              have b49850 := hb (x 9 12)
              clear * - r49844 e49845 e49846 b49847 b49848 b49849 b49850 d49835 d49814
              omega
            have d49851 : (x 7 12).toNat = 0 := by
              have r49852 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
              have e49853 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e49854 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have b49855 := hb (x 4 3)
              have b49856 := hb (x 5 2)
              have b49857 := hb (x 6 13)
              have b49858 := hb (x 7 12)
              clear * - r49852 e49853 e49854 b49855 b49856 b49857 b49858 d49797
              omega
            have d49859 : (x 5 2).toNat = 0 := by
              have r49860 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
              have e49861 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
              have e49862 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
              have b49863 := hb (x 4 3)
              have b49864 := hb (x 5 2)
              have b49865 := hb (x 6 13)
              have b49866 := hb (x 7 12)
              clear * - r49860 e49861 e49862 b49863 b49864 b49865 b49866 d49851 d49797
              omega
            have d49867 : (x 7 13).toNat = 1 := by
              have r49868 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
              have b49869 := hb (x 5 2)
              have b49870 := hb (x 7 13)
              have b49871 := hb (x 6 1 && x 6 14)
              clear * - r49868 b49869 b49870 b49871 d49740 d49859
              omega
            have d49872 : (x 7 1).toNat = 1 := by
              have r49873 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
              have b49874 := hb (x 7 1)
              have b49875 := hb (x 7 13)
              clear * - r49873 b49874 b49875 d49867
              omega
            have d49876 : (x 8 14).toNat = 0 := by
              have r49877 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
              have b49878 := hb (x 7 1)
              have b49879 := hb (x 8 14)
              clear * - r49877 b49878 b49879 d49872
              omega
            have d49880 : (x 8 1 && x 8 14).toNat = 0 := by
              have r49881 := hand2 (x 8 1) (x 8 14)
              have b49882 := hb (x 8 14)
              have b49883 := hb (x 8 1 && x 8 14)
              clear * - r49881 b49882 b49883 d49876
              omega
            have d49884 : (x 9 13).toNat = 1 := by
              have r49885 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
              have b49886 := hb (x 7 2)
              have b49887 := hb (x 9 13)
              have b49888 := hb (x 8 1 && x 8 14)
              clear * - r49885 b49886 b49887 b49888 d49880 d49843
              omega
            have d49889 : (x 9 1).toNat = 1 := by
              have r49890 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
              have b49891 := hb (x 9 1)
              have b49892 := hb (x 9 13)
              clear * - r49890 b49891 b49892 d49884
              omega
            have d49893 : (x 10 14).toNat = 0 := by
              have r49894 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
              have b49895 := hb (x 9 1)
              have b49896 := hb (x 10 14)
              clear * - r49894 b49895 b49896 d49889
              omega
            have d49897 : (x 10 1 && x 10 14).toNat = 0 := by
              have r49898 := hand2 (x 10 1) (x 10 14)
              have b49899 := hb (x 10 14)
              have b49900 := hb (x 10 1 && x 10 14)
              clear * - r49898 b49899 b49900 d49893
              omega
            have d49901 : (x 11 13).toNat = 1 := by
              have r49902 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
              have b49903 := hb (x 9 2)
              have b49904 := hb (x 11 13)
              have b49905 := hb (x 10 1 && x 10 14)
              clear * - r49902 b49903 b49904 b49905 d49897 d49831
              omega
            have d49906 : (x 11 1).toNat = 1 := by
              have r49907 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
              have b49908 := hb (x 11 1)
              have b49909 := hb (x 11 13)
              clear * - r49907 b49908 b49909 d49901
              omega
            have d49910 : (x 12 14).toNat = 0 := by
              have r49911 : (x 12 14).toNat + (x 11 1).toNat = 1 := hd14 12
              have b49912 := hb (x 11 1)
              have b49913 := hb (x 12 14)
              clear * - r49911 b49912 b49913 d49906
              omega
            have d49914 : (x 12 1 && x 12 14).toNat = 0 := by
              have r49915 := hand2 (x 12 1) (x 12 14)
              have b49916 := hb (x 12 14)
              have b49917 := hb (x 12 1 && x 12 14)
              clear * - r49915 b49916 b49917 d49910
              omega
            have d49918 : (x 12 2).toNat = 0 := by
              have r49919 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
              have b49920 := hb (x 12 2)
              have b49921 := hb (x 12 14)
              clear * - r49919 b49920 b49921 d49910
              omega
            have d49922 : (x 12 12).toNat = 0 := by
              have r49923 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
              have e49924 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e49925 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b49926 := hb (x 9 3)
              have b49927 := hb (x 10 2)
              have b49928 := hb (x 11 13)
              have b49929 := hb (x 12 12)
              clear * - r49923 e49924 e49925 b49926 b49927 b49928 b49929 d49901
              omega
            have d49930 : (x 10 2).toNat = 0 := by
              have r49931 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
              have e49932 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
              have e49933 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
              have b49934 := hb (x 9 3)
              have b49935 := hb (x 10 2)
              have b49936 := hb (x 11 13)
              have b49937 := hb (x 12 12)
              clear * - r49931 e49932 e49933 b49934 b49935 b49936 b49937 d49922 d49901
              omega
            have d49938 : (x 10 12).toNat = 0 := by
              have r49939 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
              have e49940 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
              have e49941 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
              have b49942 := hb (x 7 3)
              have b49943 := hb (x 8 2)
              have b49944 := hb (x 9 13)
              have b49945 := hb (x 10 12)
              clear * - r49939 e49940 e49941 b49942 b49943 b49944 b49945 d49884
              omega
            have d49946 : (x 8 2).toNat = 0 := by
              have r49947 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
              have e49948 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
              have e49949 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
              have b49950 := hb (x 7 3)
              have b49951 := hb (x 8 2)
              have b49952 := hb (x 9 13)
              have b49953 := hb (x 10 12)
              clear * - r49947 e49948 e49949 b49950 b49951 b49952 b49953 d49938 d49884
              omega
            have d49954 : (x 10 13).toNat = 1 := by
              have r49955 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
              have b49956 := hb (x 8 2)
              have b49957 := hb (x 10 13)
              have b49958 := hb (x 9 1 && x 9 14)
              clear * - r49955 b49956 b49957 b49958 d49827 d49946
              omega
            have d49959 : (x 10 1).toNat = 1 := by
              have r49960 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
              have b49961 := hb (x 10 1)
              have b49962 := hb (x 10 13)
              clear * - r49960 b49961 b49962 d49954
              omega
            have d49963 : (x 11 14).toNat = 0 := by
              have r49964 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
              have b49965 := hb (x 10 1)
              have b49966 := hb (x 11 14)
              clear * - r49964 b49965 b49966 d49959
              omega
            have d49967 : (x 11 1 && x 11 14).toNat = 0 := by
              have r49968 := hand2 (x 11 1) (x 11 14)
              have b49969 := hb (x 11 14)
              have b49970 := hb (x 11 1 && x 11 14)
              clear * - r49968 b49969 b49970 d49963
              omega
            have d49971 : (x 12 13).toNat = 1 := by
              have r49972 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
              have b49973 := hb (x 10 2)
              have b49974 := hb (x 12 13)
              have b49975 := hb (x 11 1 && x 11 14)
              clear * - r49972 b49973 b49974 b49975 d49967 d49930
              omega
            have d49976 : (x 12 1).toNat = 1 := by
              have r49977 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
              have b49978 := hb (x 12 1)
              have b49979 := hb (x 12 13)
              clear * - r49977 b49978 b49979 d49971
              omega
            have d49980 : (x 13 14).toNat = 0 := by
              have r49981 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
              have b49982 := hb (x 12 1)
              have b49983 := hb (x 13 14)
              clear * - r49981 b49982 b49983 d49976
              omega
            have d49984 : (x 13 1 && x 13 14).toNat = 0 := by
              have r49985 := hand2 (x 13 1) (x 13 14)
              have b49986 := hb (x 13 14)
              have b49987 := hb (x 13 1 && x 13 14)
              clear * - r49985 b49986 b49987 d49980
              omega
            have d49988 : (x 14 13).toNat = 1 := by
              have r49989 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
              have b49990 := hb (x 12 2)
              have b49991 := hb (x 14 13)
              have b49992 := hb (x 13 1 && x 13 14)
              clear * - r49989 b49990 b49991 b49992 d49984 d49918
              omega
            have d49993 : (x 14 1).toNat = 1 := by
              have r49994 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
              have b49995 := hb (x 14 1)
              have b49996 := hb (x 14 13)
              clear * - r49994 b49995 b49996 d49988
              omega
            have d49997 : (x 15 14).toNat = 0 := by
              have r49998 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
              have b49999 := hb (x 14 1)
              have b50000 := hb (x 15 14)
              clear * - r49998 b49999 b50000 d49993
              omega
            have d50001 : (x 15 1 && x 15 14).toNat = 0 := by
              have r50002 := hand2 (x 15 1) (x 15 14)
              have b50003 := hb (x 15 14)
              have b50004 := hb (x 15 1 && x 15 14)
              clear * - r50002 b50003 b50004 d49997
              omega
            have d50005 : (x 15 2).toNat = 0 := by
              have r50006 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
              have b50007 := hb (x 15 2)
              have b50008 := hb (x 15 14)
              clear * - r50006 b50007 b50008 d49997
              omega
            have d50009 : (x 15 2 && x 15 13).toNat = 0 := by
              have r50010 := hand1 (x 15 2) (x 15 13)
              have b50011 := hb (x 15 2)
              have b50012 := hb (x 15 2 && x 15 13)
              clear * - r50010 b50011 b50012 d50005
              omega
            have d50013 : (x 15 12).toNat = 0 := by
              have r50014 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
              have e50015 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e50016 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b50017 := hb (x 12 3)
              have b50018 := hb (x 13 2)
              have b50019 := hb (x 14 13)
              have b50020 := hb (x 15 12)
              clear * - r50014 e50015 e50016 b50017 b50018 b50019 b50020 d49988
              omega
            have d50021 : (x 13 2).toNat = 0 := by
              have r50022 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
              have e50023 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
              have e50024 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
              have b50025 := hb (x 12 3)
              have b50026 := hb (x 13 2)
              have b50027 := hb (x 14 13)
              have b50028 := hb (x 15 12)
              clear * - r50022 e50023 e50024 b50025 b50026 b50027 b50028 d50013 d49988
              omega
            have d50029 : (x 13 12).toNat = 0 := by
              have r50030 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
              have e50031 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e50032 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b50033 := hb (x 10 3)
              have b50034 := hb (x 11 2)
              have b50035 := hb (x 12 13)
              have b50036 := hb (x 13 12)
              clear * - r50030 e50031 e50032 b50033 b50034 b50035 b50036 d49971
              omega
            have d50037 : (x 13 4).toNat = 0 := by
              have r50038 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
              have b50039 := hb (x 13 4)
              have b50040 := hb (x 13 12)
              clear * - r50038 b50039 b50040 d50029
              omega
            have d50041 : (x 11 2).toNat = 0 := by
              have r50042 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
              have e50043 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
              have e50044 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
              have b50045 := hb (x 10 3)
              have b50046 := hb (x 11 2)
              have b50047 := hb (x 12 13)
              have b50048 := hb (x 13 12)
              clear * - r50042 e50043 e50044 b50045 b50046 b50047 b50048 d50029 d49971
              omega
            have d50049 : (x 13 13).toNat = 1 := by
              have r50050 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
              have b50051 := hb (x 11 2)
              have b50052 := hb (x 13 13)
              have b50053 := hb (x 12 1 && x 12 14)
              clear * - r50050 b50051 b50052 b50053 d49914 d50041
              omega
            have d50054 : (x 13 1).toNat = 1 := by
              have r50055 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
              have b50056 := hb (x 13 1)
              have b50057 := hb (x 13 13)
              clear * - r50055 b50056 b50057 d50049
              omega
            have d50058 : (x 14 14).toNat = 0 := by
              have r50059 : (x 14 14).toNat + (x 13 1).toNat = 1 := hd14 14
              have b50060 := hb (x 13 1)
              have b50061 := hb (x 14 14)
              clear * - r50059 b50060 b50061 d50054
              omega
            have d50062 : (x 14 1 && x 14 14).toNat = 0 := by
              have r50063 := hand2 (x 14 1) (x 14 14)
              have b50064 := hb (x 14 14)
              have b50065 := hb (x 14 1 && x 14 14)
              clear * - r50063 b50064 b50065 d50058
              omega
            have d50066 : (x 15 13).toNat = 1 := by
              have r50067 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
              have b50068 := hb (x 13 2)
              have b50069 := hb (x 15 13)
              have b50070 := hb (x 14 1 && x 14 14)
              clear * - r50067 b50068 b50069 b50070 d50062 d50021
              omega
            have d50071 : (x 15 1).toNat = 1 := by
              have r50072 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
              have b50073 := hb (x 15 1)
              have b50074 := hb (x 15 13)
              clear * - r50072 b50073 b50074 d50066
              omega
            have d50075 : (x 16 14).toNat = 0 := by
              have r50076 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
              have b50077 := hb (x 15 1)
              have b50078 := hb (x 16 14)
              clear * - r50076 b50077 b50078 d50071
              omega
            have d50079 : (x 16 1 && x 16 14).toNat = 0 := by
              have r50080 := hand2 (x 16 1) (x 16 14)
              have b50081 := hb (x 16 14)
              have b50082 := hb (x 16 1 && x 16 14)
              clear * - r50080 b50081 b50082 d50075
              omega
            have d50083 : (x 17 13).toNat = 1 := by
              have r50084 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
              have b50085 := hb (x 15 2)
              have b50086 := hb (x 17 13)
              have b50087 := hb (x 16 1 && x 16 14)
              clear * - r50084 b50085 b50086 b50087 d50079 d50005
              omega
            have d50088 : (x 17 1).toNat = 1 := by
              have r50089 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
              have b50090 := hb (x 17 1)
              have b50091 := hb (x 17 13)
              clear * - r50089 b50090 b50091 d50083
              omega
            have d50092 : (x 18 14).toNat = 0 := by
              have r50093 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
              have b50094 := hb (x 17 1)
              have b50095 := hb (x 18 14)
              clear * - r50093 b50094 b50095 d50088
              omega
            have d50096 : (x 18 1 && x 18 14).toNat = 0 := by
              have r50097 := hand2 (x 18 1) (x 18 14)
              have b50098 := hb (x 18 14)
              have b50099 := hb (x 18 1 && x 18 14)
              clear * - r50097 b50098 b50099 d50092
              omega
            have d50100 : (x 18 2).toNat = 0 := by
              have r50101 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
              have b50102 := hb (x 18 2)
              have b50103 := hb (x 18 14)
              clear * - r50101 b50102 b50103 d50092
              omega
            have d50104 : (x 18 12).toNat = 0 := by
              have r50105 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
              have e50106 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
              have e50107 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
              have b50108 := hb (x 15 3)
              have b50109 := hb (x 16 2)
              have b50110 := hb (x 17 13)
              have b50111 := hb (x 18 12)
              clear * - r50105 e50106 e50107 b50108 b50109 b50110 b50111 d50083
              omega
            have d50112 : (x 16 2).toNat = 0 := by
              have r50113 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
              have e50114 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
              have e50115 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
              have b50116 := hb (x 15 3)
              have b50117 := hb (x 16 2)
              have b50118 := hb (x 17 13)
              have b50119 := hb (x 18 12)
              clear * - r50113 e50114 e50115 b50116 b50117 b50118 b50119 d50104 d50083
              omega
            have d50120 : (x 16 12).toNat = 0 := by
              have r50121 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
              have e50122 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e50123 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b50124 := hb (x 13 3)
              have b50125 := hb (x 14 2)
              have b50126 := hb (x 15 13)
              have b50127 := hb (x 16 12)
              clear * - r50121 e50122 e50123 b50124 b50125 b50126 b50127 d50066
              omega
            have d50128 : (x 16 1 && x 16 12).toNat = 0 := by
              have r50129 := hand2 (x 16 1) (x 16 12)
              have b50130 := hb (x 16 12)
              have b50131 := hb (x 16 1 && x 16 12)
              clear * - r50129 b50130 b50131 d50120
              omega
            have d50132 : (x 14 2).toNat = 0 := by
              have r50133 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
              have e50134 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
              have e50135 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
              have b50136 := hb (x 13 3)
              have b50137 := hb (x 14 2)
              have b50138 := hb (x 15 13)
              have b50139 := hb (x 16 12)
              clear * - r50133 e50134 e50135 b50136 b50137 b50138 b50139 d50120 d50066
              omega
            have d50140 : (x 16 13).toNat = 1 := by
              have r50141 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
              have b50142 := hb (x 14 2)
              have b50143 := hb (x 16 13)
              have b50144 := hb (x 15 1 && x 15 14)
              clear * - r50141 b50142 b50143 b50144 d50001 d50132
              omega
            have d50145 : (x 16 1).toNat = 1 := by
              have r50146 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
              have b50147 := hb (x 16 1)
              have b50148 := hb (x 16 13)
              clear * - r50146 b50147 b50148 d50140
              omega
            have d50149 : (x 17 14).toNat = 0 := by
              have r50150 : (x 17 14).toNat + (x 16 1).toNat = 1 := hd14 17
              have b50151 := hb (x 16 1)
              have b50152 := hb (x 17 14)
              clear * - r50150 b50151 b50152 d50145
              omega
            have d50153 : (x 17 1 && x 17 14).toNat = 0 := by
              have r50154 := hand2 (x 17 1) (x 17 14)
              have b50155 := hb (x 17 14)
              have b50156 := hb (x 17 1 && x 17 14)
              clear * - r50154 b50155 b50156 d50149
              omega
            have d50157 : (x 18 13).toNat = 1 := by
              have r50158 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := hcov13 18
              have b50159 := hb (x 16 2)
              have b50160 := hb (x 18 13)
              have b50161 := hb (x 17 1 && x 17 14)
              clear * - r50158 b50159 b50160 b50161 d50153 d50112
              omega
            have d50162 : (x 19 12).toNat = 0 := by
              have r50163 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
              have e50164 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e50165 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b50166 := hb (x 16 3)
              have b50167 := hb (x 17 2)
              have b50168 := hb (x 18 13)
              have b50169 := hb (x 19 12)
              clear * - r50163 e50164 e50165 b50166 b50167 b50168 b50169 d50157
              omega
            have d50170 : (x 17 2).toNat = 0 := by
              have r50171 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
              have e50172 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
              have e50173 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
              have b50174 := hb (x 16 3)
              have b50175 := hb (x 17 2)
              have b50176 := hb (x 18 13)
              have b50177 := hb (x 19 12)
              clear * - r50171 e50172 e50173 b50174 b50175 b50176 b50177 d50162 d50157
              omega
            have d50178 : (x 19 13).toNat = 1 := by
              have r50179 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
              have b50180 := hb (x 17 2)
              have b50181 := hb (x 19 13)
              have b50182 := hb (x 18 1 && x 18 14)
              clear * - r50179 b50180 b50181 b50182 d50096 d50170
              omega
            have d50183 : (x 20 12).toNat = 0 := by
              have r50184 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
              have e50185 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e50186 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b50187 := hb (x 17 3)
              have b50188 := hb (x 18 2)
              have b50189 := hb (x 19 13)
              have b50190 := hb (x 20 12)
              clear * - r50184 e50185 e50186 b50187 b50188 b50189 b50190 d50178 d50100
              omega
            have d50191 : (x 17 3).toNat = 0 := by
              have r50192 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
              have e50193 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
              have e50194 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
              have b50195 := hb (x 17 3)
              have b50196 := hb (x 18 2)
              have b50197 := hb (x 19 13)
              have b50198 := hb (x 20 12)
              clear * - r50192 e50193 e50194 b50195 b50196 b50197 b50198 d50183 d50178 d50100
              omega
            have d50199 : (x 17 11).toNat = 0 := by
              have r50200 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
              have b50201 := hb (x 17 3)
              have b50202 := hb (x 17 11)
              clear * - r50200 b50201 b50202 d50191
              omega
            have d50203 : (x 17 12).toNat = 0 := by
              have r50204 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
              have e50205 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e50206 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b50207 := hb (x 14 3)
              have b50208 := hb (x 15 2)
              have b50209 := hb (x 16 13)
              have b50210 := hb (x 17 12)
              clear * - r50204 e50205 e50206 b50207 b50208 b50209 b50210 d50140 d50005
              omega
            have d50211 : (x 14 3).toNat = 0 := by
              have r50212 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
              have e50213 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
              have e50214 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
              have b50215 := hb (x 14 3)
              have b50216 := hb (x 15 2)
              have b50217 := hb (x 16 13)
              have b50218 := hb (x 17 12)
              clear * - r50212 e50213 e50214 b50215 b50216 b50217 b50218 d50203 d50140 d50005
              omega
            have d50219 : (x 14 3 && x 14 14).toNat = 0 := by
              have r50220 := hand1 (x 14 3) (x 14 14)
              have b50221 := hb (x 14 3)
              have b50222 := hb (x 14 3 && x 14 14)
              clear * - r50220 b50221 b50222 d50211
              omega
            have r50223 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
            have b50224 := hb (x 13 4)
            have b50225 := hb (x 17 11)
            have b50226 := hb (x 16 1 && x 16 12)
            have b50227 := hb (x 15 2 && x 15 13)
            have b50228 := hb (x 14 3 && x 14 14)
            linarith only [r50223, b50224, b50225, b50226, b50227, b50228, d50199, d50128, d50009, d50219, d50037]
        · have f50229 : (x 0 9).toNat = 1 := by rw [h49285]; rfl
          have d50230 : (x 1 8).toNat = 0 := by
            have r50231 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
            have e50232 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e50233 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e50234 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e50235 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e50236 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e50237 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b50238 := hb (x (-6) 7)
            have b50239 := hb (x (-5) 6)
            have b50240 := hb (x (-4) 5)
            have b50241 := hb (x (-3) 4)
            have b50242 := hb (x (-2) 11)
            have b50243 := hb (x (-1) 10)
            have b50244 := hb (x 0 9)
            have b50245 := hb (x 1 8)
            clear * - r50231 e50232 e50233 e50234 e50235 e50236 e50237 b50238 b50239 b50240 b50241 b50242 b50243 b50244 b50245 f50229
            omega
          have d50246 : (x (-1) 10).toNat = 0 := by
            have r50247 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
            have e50248 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e50249 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e50250 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e50251 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e50252 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e50253 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b50254 := hb (x (-6) 7)
            have b50255 := hb (x (-5) 6)
            have b50256 := hb (x (-4) 5)
            have b50257 := hb (x (-3) 4)
            have b50258 := hb (x (-2) 11)
            have b50259 := hb (x (-1) 10)
            have b50260 := hb (x 0 9)
            have b50261 := hb (x 1 8)
            clear * - r50247 e50248 e50249 e50250 e50251 e50252 e50253 b50254 b50255 b50256 b50257 b50258 b50259 b50260 b50261 d50230 f50229
            omega
          have d50262 : (x (-2) 11).toNat = 0 := by
            have r50263 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
            have e50264 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e50265 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e50266 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e50267 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e50268 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e50269 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b50270 := hb (x (-6) 7)
            have b50271 := hb (x (-5) 6)
            have b50272 := hb (x (-4) 5)
            have b50273 := hb (x (-3) 4)
            have b50274 := hb (x (-2) 11)
            have b50275 := hb (x (-1) 10)
            have b50276 := hb (x 0 9)
            have b50277 := hb (x 1 8)
            clear * - r50263 e50264 e50265 e50266 e50267 e50268 e50269 b50270 b50271 b50272 b50273 b50274 b50275 b50276 b50277 d50230 f50229 d50246
            omega
          have d50278 : (x (-3) 4).toNat = 0 := by
            have r50279 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
            have e50280 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e50281 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e50282 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e50283 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e50284 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e50285 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b50286 := hb (x (-6) 7)
            have b50287 := hb (x (-5) 6)
            have b50288 := hb (x (-4) 5)
            have b50289 := hb (x (-3) 4)
            have b50290 := hb (x (-2) 11)
            have b50291 := hb (x (-1) 10)
            have b50292 := hb (x 0 9)
            have b50293 := hb (x 1 8)
            clear * - r50279 e50280 e50281 e50282 e50283 e50284 e50285 b50286 b50287 b50288 b50289 b50290 b50291 b50292 b50293 d50230 f50229 d50246 d50262
            omega
          have d50294 : (x (-3) 4 && x (-3) 14).toNat = 0 := by
            have r50295 := hand1 (x (-3) 4) (x (-3) 14)
            have b50296 := hb (x (-3) 4)
            have b50297 := hb (x (-3) 4 && x (-3) 14)
            clear * - r50295 b50296 b50297 d50278
            omega
          have d50298 : (x (-4) 5).toNat = 0 := by
            have r50299 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := hd8 1
            have e50300 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
            have e50301 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
            have e50302 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
            have e50303 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
            have e50304 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
            have e50305 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
            have b50306 := hb (x (-6) 7)
            have b50307 := hb (x (-5) 6)
            have b50308 := hb (x (-4) 5)
            have b50309 := hb (x (-3) 4)
            have b50310 := hb (x (-2) 11)
            have b50311 := hb (x (-1) 10)
            have b50312 := hb (x 0 9)
            have b50313 := hb (x 1 8)
            clear * - r50299 e50300 e50301 e50302 e50303 e50304 e50305 b50306 b50307 b50308 b50309 b50310 b50311 b50312 b50313 d50230 f50229 d50246 d50262 d50278
            omega
          have r50314 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
          have e50315 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e50316 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have r50317 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
          have e50318 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e50319 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have r50320 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
          have r50321 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := hcov10 1
          have r50322 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
          have r50323 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := hcov13 0
          have r50324 := hand1 (x (-1) 2) (x (-1) 12)
          have r50325 := hand2 (x (-1) 2) (x (-1) 12)
          have r50326 := hand1 (x (-2) 3) (x (-2) 13)
          have r50327 := hand2 (x (-2) 3) (x (-2) 13)
          have r50328 := hand1 (x (-2) 1) (x (-2) 14)
          have r50329 := hand2 (x (-1) 1) (x (-1) 14)
          have b50330 := hb (x (-4) 3)
          have b50331 := hb (x (-4) 5)
          have b50332 := hb (x (-3) 2)
          have b50333 := hb (x (-2) 1)
          have b50334 := hb (x (-2) 2)
          have b50335 := hb (x (-2) 3)
          have b50336 := hb (x (-2) 13)
          have b50337 := hb (x (-1) 2)
          have b50338 := hb (x (-1) 12)
          have b50339 := hb (x (-1) 13)
          have b50340 := hb (x (-1) 14)
          have b50341 := hb (x 0 13)
          have b50342 := hb (x 1 10)
          have b50343 := hb (x 1 12)
          have b50344 := hb (x 0 1 && x 0 11)
          have b50345 := hb (x (-1) 2 && x (-1) 12)
          have b50346 := hb (x (-2) 3 && x (-2) 13)
          have b50347 := hb (x (-3) 4 && x (-3) 14)
          have b50348 := hb (x (-2) 1 && x (-2) 14)
          have b50349 := hb (x (-1) 1 && x (-1) 14)
          linarith only [r50314, e50315, e50316, r50317, e50318, e50319, r50320, r50321, r50322, r50323, r50324, r50325, r50326, r50327, r50328, r50329, b50330, b50331, b50332, b50333, b50334, b50335, b50336, b50337, b50338, b50339, b50340, b50341, b50342, b50343, b50344, b50345, b50346, b50347, b50348, b50349, d50298, d49187, d49171, g6, g12, d50294]
      · have f50350 : (x 0 8).toNat = 1 := by rw [h49283]; rfl
        have d50351 : (x (-1) 9).toNat = 0 := by
          have r50352 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e50353 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e50354 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e50355 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e50356 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e50357 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e50358 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b50359 := hb (x (-7) 7)
          have b50360 := hb (x (-6) 6)
          have b50361 := hb (x (-5) 5)
          have b50362 := hb (x (-4) 4)
          have b50363 := hb (x (-3) 11)
          have b50364 := hb (x (-2) 10)
          have b50365 := hb (x (-1) 9)
          have b50366 := hb (x 0 8)
          clear * - r50352 e50353 e50354 e50355 e50356 e50357 e50358 b50359 b50360 b50361 b50362 b50363 b50364 b50365 b50366 f50350 d49203 d49223
          omega
        have d50367 : (x (-4) 4).toNat = 0 := by
          have r50368 : (x 0 8).toNat + (x (-1) 1 && x (-1) 9).toNat + (x (-2) 2 && x (-2) 10).toNat + (x (-3) 3 && x (-3) 11).toNat + (x (-4) 4 && x (-4) 12).toNat + (x (-5) 5 && x (-5) 13).toNat + (x (-6) 6 && x (-6) 14).toNat + (x (-7) 7).toNat = 1 := hd8 0
          have e50369 : (x (-1) 1 && x (-1) 9).toNat = (x (-1) 9).toNat := handr _ _ (fun h => hp9 (-1) (h))
          have e50370 : (x (-2) 2 && x (-2) 10).toNat = (x (-2) 10).toNat := handr _ _ (fun h => hp10 (-2) (h))
          have e50371 : (x (-3) 3 && x (-3) 11).toNat = (x (-3) 11).toNat := handr _ _ (fun h => hp11 (-3) (h))
          have e50372 : (x (-4) 4 && x (-4) 12).toNat = (x (-4) 4).toNat := handl _ _ (fun h => hp4 (-4) (h))
          have e50373 : (x (-5) 5 && x (-5) 13).toNat = (x (-5) 5).toNat := handl _ _ (fun h => hp5 (-5) (h))
          have e50374 : (x (-6) 6 && x (-6) 14).toNat = (x (-6) 6).toNat := handl _ _ (fun h => hp6 (-6) (h))
          have b50375 := hb (x (-7) 7)
          have b50376 := hb (x (-6) 6)
          have b50377 := hb (x (-5) 5)
          have b50378 := hb (x (-4) 4)
          have b50379 := hb (x (-3) 11)
          have b50380 := hb (x (-2) 10)
          have b50381 := hb (x (-1) 9)
          have b50382 := hb (x 0 8)
          clear * - r50368 e50369 e50370 e50371 e50372 e50373 e50374 b50375 b50376 b50377 b50378 b50379 b50380 b50381 b50382 f50350 d50351 d49203 d49223
          omega
        have d50383 : (x (-1) 1 && x (-1) 12).toNat = 1 := by
          have r50384 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
          have b50385 := hb (x (-4) 4)
          have b50386 := hb (x 0 11)
          have b50387 := hb (x (-1) 1 && x (-1) 12)
          have b50388 := hb (x (-2) 2 && x (-2) 13)
          have b50389 := hb (x (-3) 3 && x (-3) 14)
          clear * - r50384 b50385 b50386 b50387 b50388 b50389 g3 d49195 d49215 d50367
          omega
        have d50390 : (x (-1) 12).toNat = 1 := by
          have r50391 := hand2 (x (-1) 1) (x (-1) 12)
          have b50392 := hb (x (-1) 12)
          have b50393 := hb (x (-1) 1 && x (-1) 12)
          clear * - r50391 b50392 b50393 d50383
          omega
        have d50394 : (x (-2) 13).toNat = 0 := by
          have r50395 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
          have e50396 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
          have e50397 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
          have b50398 := hb (x (-4) 3)
          have b50399 := hb (x (-3) 2)
          have b50400 := hb (x (-2) 13)
          have b50401 := hb (x (-1) 12)
          clear * - r50395 e50396 e50397 b50398 b50399 b50400 b50401 d50390
          omega
        have d50402 : (x (-2) 5).toNat = 0 := by
          have r50403 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
          have b50404 := hb (x (-2) 5)
          have b50405 := hb (x (-2) 13)
          clear * - r50403 b50404 b50405 d50394
          omega
        have d50406 : (x (-2) 5 && x (-2) 14).toNat = 0 := by
          have r50407 := hand1 (x (-2) 5) (x (-2) 14)
          have b50408 := hb (x (-2) 5)
          have b50409 := hb (x (-2) 5 && x (-2) 14)
          clear * - r50407 b50408 b50409 d50402
          omega
        have d50410 : (x (-3) 6).toNat = 1 := by
          have r50411 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := hcov9 3
          have b50412 := hb (x (-3) 6)
          have b50413 := hb (x 3 9)
          have b50414 := hb (x 2 1 && x 2 10)
          have b50415 := hb (x 1 2 && x 1 11)
          have b50416 := hb (x 0 3 && x 0 12)
          have b50417 := hb (x (-1) 4 && x (-1) 13)
          have b50418 := hb (x (-2) 5 && x (-2) 14)
          clear * - r50411 b50412 b50413 b50414 b50415 b50416 b50417 b50418 d49243 d49275 g10 g11 d49179 d50406
          omega
        have d50419 : (x 3 8).toNat = 0 := by
          have r50420 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
          have e50421 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e50422 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e50423 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e50424 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e50425 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e50426 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b50427 := hb (x (-4) 7)
          have b50428 := hb (x (-3) 6)
          have b50429 := hb (x (-2) 5)
          have b50430 := hb (x (-1) 4)
          have b50431 := hb (x 0 11)
          have b50432 := hb (x 1 10)
          have b50433 := hb (x 2 9)
          have b50434 := hb (x 3 8)
          clear * - r50420 e50421 e50422 e50423 e50424 e50425 e50426 b50427 b50428 b50429 b50430 b50431 b50432 b50433 b50434 g6 g3 d50402 d50410
          omega
        have d50435 : (x 2 9).toNat = 0 := by
          have r50436 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
          have e50437 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e50438 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e50439 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e50440 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e50441 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e50442 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b50443 := hb (x (-4) 7)
          have b50444 := hb (x (-3) 6)
          have b50445 := hb (x (-2) 5)
          have b50446 := hb (x (-1) 4)
          have b50447 := hb (x 0 11)
          have b50448 := hb (x 1 10)
          have b50449 := hb (x 2 9)
          have b50450 := hb (x 3 8)
          clear * - r50436 e50437 e50438 e50439 e50440 e50441 e50442 b50443 b50444 b50445 b50446 b50447 b50448 b50449 b50450 d50419 g6 g3 d50402 d50410
          omega
        have d50451 : (x (-1) 4).toNat = 0 := by
          have r50452 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := hd8 3
          have e50453 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e50454 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e50455 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e50456 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e50457 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e50458 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b50459 := hb (x (-4) 7)
          have b50460 := hb (x (-3) 6)
          have b50461 := hb (x (-2) 5)
          have b50462 := hb (x (-1) 4)
          have b50463 := hb (x 0 11)
          have b50464 := hb (x 1 10)
          have b50465 := hb (x 2 9)
          have b50466 := hb (x 3 8)
          clear * - r50452 e50453 e50454 e50455 e50456 e50457 e50458 b50459 b50460 b50461 b50462 b50463 b50464 b50465 b50466 d50419 d50435 g6 g3 d50402 d50410
          omega
        have d50467 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
          have r50468 := hand1 (x (-1) 4) (x (-1) 14)
          have b50469 := hb (x (-1) 4)
          have b50470 := hb (x (-1) 4 && x (-1) 14)
          clear * - r50468 b50469 b50470 d50451
          omega
        have d50471 : (x 2 1 && x 2 11).toNat = 1 := by
          have r50472 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := hcov10 3
          have b50473 := hb (x (-2) 5)
          have b50474 := hb (x 3 10)
          have b50475 := hb (x 2 1 && x 2 11)
          have b50476 := hb (x 1 2 && x 1 12)
          have b50477 := hb (x 0 3 && x 0 13)
          have b50478 := hb (x (-1) 4 && x (-1) 14)
          clear * - r50472 b50473 b50474 b50475 b50476 b50477 b50478 g9 g13 g14 d50467 d50402
          omega
        have d50479 : (x 2 11).toNat = 1 := by
          have r50480 := hand2 (x 2 1) (x 2 11)
          have b50481 := hb (x 2 11)
          have b50482 := hb (x 2 1 && x 2 11)
          clear * - r50480 b50481 b50482 d50471
          omega
        have d50483 : (x 2 3).toNat = 1 := by
          have r50484 : (x 2 11).toNat ≤ (x 2 3).toNat := himp _ _ (hp11 2)
          have b50485 := hb (x 2 3)
          have b50486 := hb (x 2 11)
          clear * - r50484 b50485 b50486 d50479
          omega
        have d50487 : (x 5 12).toNat = 0 := by
          have r50488 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
          have e50489 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e50490 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b50491 := hb (x 2 3)
          have b50492 := hb (x 3 2)
          have b50493 := hb (x 4 13)
          have b50494 := hb (x 5 12)
          clear * - r50488 e50489 e50490 b50491 b50492 b50493 b50494 g7 d50483
          omega
        have d50495 : (x 4 13).toNat = 0 := by
          have r50496 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
          have e50497 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
          have e50498 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
          have b50499 := hb (x 2 3)
          have b50500 := hb (x 3 2)
          have b50501 := hb (x 4 13)
          have b50502 := hb (x 5 12)
          clear * - r50496 e50497 e50498 b50499 b50500 b50501 b50502 d50487 g7 d50483
          omega
        have d50503 : (x 2 2).toNat = 1 := by
          have r50504 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
          have b50505 := hb (x 2 2)
          have b50506 := hb (x 4 13)
          have b50507 := hb (x 3 1 && x 3 14)
          clear * - r50504 b50505 b50506 b50507 d50495 g20
          omega
        have d50508 : (x 2 14).toNat = 1 := by
          have r50509 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
          have b50510 := hb (x 2 2)
          have b50511 := hb (x 2 14)
          clear * - r50509 b50510 b50511 d50503
          omega
        have d50512 : (x 1 1).toNat = 0 := by
          have r50513 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
          have b50514 := hb (x 1 1)
          have b50515 := hb (x 2 14)
          clear * - r50513 b50514 b50515 d50508
          omega
        have d50516 : (x 1 13).toNat = 0 := by
          have r50517 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
          have b50518 := hb (x 1 1)
          have b50519 := hb (x 1 13)
          clear * - r50517 b50518 b50519 d50512
          omega
        have d50520 : (x (-1) 2).toNat = 1 := by
          have r50521 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
          have b50522 := hb (x (-1) 2)
          have b50523 := hb (x 1 13)
          have b50524 := hb (x 0 1 && x 0 14)
          clear * - r50521 b50522 b50523 b50524 d50516 g19
          omega
        have d50525 : (x (-1) 14).toNat = 1 := by
          have r50526 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
          have b50527 := hb (x (-1) 2)
          have b50528 := hb (x (-1) 14)
          clear * - r50526 b50527 b50528 d50520
          omega
        have d50529 : (x (-2) 1).toNat = 0 := by
          have r50530 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
          have b50531 := hb (x (-2) 1)
          have b50532 := hb (x (-1) 14)
          clear * - r50530 b50531 b50532 d50525
          omega
        have d50533 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
          have r50534 := hand1 (x (-2) 1) (x (-2) 14)
          have b50535 := hb (x (-2) 1)
          have b50536 := hb (x (-2) 1 && x (-2) 14)
          clear * - r50534 b50535 b50536 d50529
          omega
        have d50537 : (x (-3) 2).toNat = 1 := by
          have r50538 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
          have b50539 := hb (x (-3) 2)
          have b50540 := hb (x (-1) 13)
          have b50541 := hb (x (-2) 1 && x (-2) 14)
          clear * - r50538 b50539 b50540 b50541 d49171 d50533
          omega
        have r50542 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
        have e50543 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e50544 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b50545 := hb (x (-4) 3)
        have b50546 := hb (x (-3) 2)
        have b50547 := hb (x (-2) 13)
        have b50548 := hb (x (-1) 12)
        linarith only [r50542, e50543, e50544, b50545, b50546, b50547, b50548, d50390, d50394, d50537]
    · have f50549 : (x 0 7).toNat = 1 := by rw [h49281]; rfl
      have d50550 : (x 7 8).toNat = 0 := by
        have r50551 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
        have e50552 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e50553 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e50554 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e50555 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e50556 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e50557 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b50558 := hb (x 0 7)
        have b50559 := hb (x 1 6)
        have b50560 := hb (x 2 5)
        have b50561 := hb (x 3 4)
        have b50562 := hb (x 4 11)
        have b50563 := hb (x 5 10)
        have b50564 := hb (x 6 9)
        have b50565 := hb (x 7 8)
        clear * - r50551 e50552 e50553 e50554 e50555 e50556 e50557 b50558 b50559 b50560 b50561 b50562 b50563 b50564 b50565 g8 g5 f50549
        omega
      have d50566 : (x 6 9).toNat = 0 := by
        have r50567 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
        have e50568 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e50569 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e50570 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e50571 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e50572 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e50573 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b50574 := hb (x 0 7)
        have b50575 := hb (x 1 6)
        have b50576 := hb (x 2 5)
        have b50577 := hb (x 3 4)
        have b50578 := hb (x 4 11)
        have b50579 := hb (x 5 10)
        have b50580 := hb (x 6 9)
        have b50581 := hb (x 7 8)
        clear * - r50567 e50568 e50569 e50570 e50571 e50572 e50573 b50574 b50575 b50576 b50577 b50578 b50579 b50580 b50581 d50550 g8 g5 f50549
        omega
      have d50582 : (x 5 10).toNat = 0 := by
        have r50583 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
        have e50584 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e50585 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e50586 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e50587 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e50588 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e50589 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b50590 := hb (x 0 7)
        have b50591 := hb (x 1 6)
        have b50592 := hb (x 2 5)
        have b50593 := hb (x 3 4)
        have b50594 := hb (x 4 11)
        have b50595 := hb (x 5 10)
        have b50596 := hb (x 6 9)
        have b50597 := hb (x 7 8)
        clear * - r50583 e50584 e50585 e50586 e50587 e50588 e50589 b50590 b50591 b50592 b50593 b50594 b50595 b50596 b50597 d50550 d50566 g8 g5 f50549
        omega
      have d50598 : (x 4 11).toNat = 0 := by
        have r50599 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := hd8 7
        have e50600 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
        have e50601 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
        have e50602 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
        have e50603 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
        have e50604 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
        have e50605 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
        have b50606 := hb (x 0 7)
        have b50607 := hb (x 1 6)
        have b50608 := hb (x 2 5)
        have b50609 := hb (x 3 4)
        have b50610 := hb (x 4 11)
        have b50611 := hb (x 5 10)
        have b50612 := hb (x 6 9)
        have b50613 := hb (x 7 8)
        clear * - r50599 e50600 e50601 e50602 e50603 e50604 e50605 b50606 b50607 b50608 b50609 b50610 b50611 b50612 b50613 d50550 d50566 d50582 g8 g5 f50549
        omega
      have d50614 : (x 4 1 && x 4 11).toNat = 0 := by
        have r50615 := hand2 (x 4 1) (x 4 11)
        have b50616 := hb (x 4 11)
        have b50617 := hb (x 4 1 && x 4 11)
        clear * - r50615 b50616 b50617 d50598
        omega
      have d50618 : (x 2 3 && x 2 13).toNat = 1 := by
        have r50619 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := hcov10 5
        have b50620 := hb (x 0 5)
        have b50621 := hb (x 5 10)
        have b50622 := hb (x 4 1 && x 4 11)
        have b50623 := hb (x 3 2 && x 3 12)
        have b50624 := hb (x 2 3 && x 2 13)
        have b50625 := hb (x 1 4 && x 1 14)
        clear * - r50619 b50620 b50621 b50622 b50623 b50624 b50625 d50582 d50614 g15 g16 f49280
        omega
      have d50626 : (x 2 3).toNat = 1 := by
        have r50627 := hand1 (x 2 3) (x 2 13)
        have b50628 := hb (x 2 3)
        have b50629 := hb (x 2 3 && x 2 13)
        clear * - r50627 b50628 b50629 d50618
        omega
      have d50630 : (x 5 12).toNat = 0 := by
        have r50631 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
        have e50632 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e50633 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b50634 := hb (x 2 3)
        have b50635 := hb (x 3 2)
        have b50636 := hb (x 4 13)
        have b50637 := hb (x 5 12)
        clear * - r50631 e50632 e50633 b50634 b50635 b50636 b50637 g7 d50626
        omega
      have d50638 : (x 4 13).toNat = 0 := by
        have r50639 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := hd12 5
        have e50640 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e50641 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b50642 := hb (x 2 3)
        have b50643 := hb (x 3 2)
        have b50644 := hb (x 4 13)
        have b50645 := hb (x 5 12)
        clear * - r50639 e50640 e50641 b50642 b50643 b50644 b50645 d50630 g7 d50626
        omega
      have d50646 : (x 2 2).toNat = 1 := by
        have r50647 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
        have b50648 := hb (x 2 2)
        have b50649 := hb (x 4 13)
        have b50650 := hb (x 3 1 && x 3 14)
        clear * - r50647 b50648 b50649 b50650 d50638 g20
        omega
      have d50651 : (x 2 14).toNat = 1 := by
        have r50652 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
        have b50653 := hb (x 2 2)
        have b50654 := hb (x 2 14)
        clear * - r50652 b50653 b50654 d50646
        omega
      have d50655 : (x 1 1).toNat = 0 := by
        have r50656 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
        have b50657 := hb (x 1 1)
        have b50658 := hb (x 2 14)
        clear * - r50656 b50657 b50658 d50651
        omega
      have d50659 : (x 1 13).toNat = 0 := by
        have r50660 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
        have b50661 := hb (x 1 1)
        have b50662 := hb (x 1 13)
        clear * - r50660 b50661 b50662 d50655
        omega
      have d50663 : (x (-1) 2).toNat = 1 := by
        have r50664 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
        have b50665 := hb (x (-1) 2)
        have b50666 := hb (x 1 13)
        have b50667 := hb (x 0 1 && x 0 14)
        clear * - r50664 b50665 b50666 b50667 d50659 g19
        omega
      have d50668 : (x (-1) 14).toNat = 1 := by
        have r50669 : (x (-1) 2).toNat ≤ (x (-1) 14).toNat := himp _ _ (hp2 (-1))
        have b50670 := hb (x (-1) 2)
        have b50671 := hb (x (-1) 14)
        clear * - r50669 b50670 b50671 d50663
        omega
      have d50672 : (x (-2) 1).toNat = 0 := by
        have r50673 : (x (-1) 14).toNat + (x (-2) 1).toNat = 1 := hd14 (-1)
        have b50674 := hb (x (-2) 1)
        have b50675 := hb (x (-1) 14)
        clear * - r50673 b50674 b50675 d50668
        omega
      have d50676 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
        have r50677 := hand1 (x (-2) 1) (x (-2) 14)
        have b50678 := hb (x (-2) 1)
        have b50679 := hb (x (-2) 1 && x (-2) 14)
        clear * - r50677 b50678 b50679 d50672
        omega
      have d50680 : (x (-3) 2).toNat = 1 := by
        have r50681 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := hcov13 (-1)
        have b50682 := hb (x (-3) 2)
        have b50683 := hb (x (-1) 13)
        have b50684 := hb (x (-2) 1 && x (-2) 14)
        clear * - r50681 b50682 b50683 b50684 d49171 d50676
        omega
      have d50685 : (x (-3) 14).toNat = 1 := by
        have r50686 : (x (-3) 2).toNat ≤ (x (-3) 14).toNat := himp _ _ (hp2 (-3))
        have b50687 := hb (x (-3) 2)
        have b50688 := hb (x (-3) 14)
        clear * - r50686 b50687 b50688 d50680
        omega
      have d50689 : (x (-4) 1).toNat = 0 := by
        have r50690 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := hd14 (-3)
        have b50691 := hb (x (-4) 1)
        have b50692 := hb (x (-3) 14)
        clear * - r50690 b50691 b50692 d50685
        omega
      have d50693 : (x (-4) 1 && x (-4) 12).toNat = 0 := by
        have r50694 := hand1 (x (-4) 1) (x (-4) 12)
        have b50695 := hb (x (-4) 1)
        have b50696 := hb (x (-4) 1 && x (-4) 12)
        clear * - r50694 b50695 b50696 d50689
        omega
      have d50697 : (x (-4) 13).toNat = 0 := by
        have r50698 : (x (-4) 13).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp13 (-4))
        have b50699 := hb (x (-4) 1)
        have b50700 := hb (x (-4) 13)
        clear * - r50698 b50699 b50700 d50689
        omega
      have d50701 : (x (-4) 5).toNat = 0 := by
        have r50702 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
        have b50703 := hb (x (-4) 5)
        have b50704 := hb (x (-4) 13)
        clear * - r50702 b50703 b50704 d50697
        omega
      have d50705 : (x (-4) 9).toNat = 0 := by
        have r50706 : (x (-4) 9).toNat ≤ (x (-4) 1).toNat := himp _ _ (hp9 (-4))
        have b50707 := hb (x (-4) 1)
        have b50708 := hb (x (-4) 9)
        clear * - r50706 b50707 b50708 d50689
        omega
      have d50709 : (x (-1) 12).toNat = 0 := by
        have r50710 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
        have e50711 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e50712 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b50713 := hb (x (-4) 3)
        have b50714 := hb (x (-3) 2)
        have b50715 := hb (x (-2) 13)
        have b50716 := hb (x (-1) 12)
        clear * - r50710 e50711 e50712 b50713 b50714 b50715 b50716 d50680
        omega
      have d50717 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
        have r50718 := hand2 (x (-1) 1) (x (-1) 12)
        have b50719 := hb (x (-1) 12)
        have b50720 := hb (x (-1) 1 && x (-1) 12)
        clear * - r50718 b50719 b50720 d50709
        omega
      have d50721 : (x (-4) 4).toNat = 1 := by
        have r50722 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := hcov11 0
        have b50723 := hb (x (-4) 4)
        have b50724 := hb (x 0 11)
        have b50725 := hb (x (-1) 1 && x (-1) 12)
        have b50726 := hb (x (-2) 2 && x (-2) 13)
        have b50727 := hb (x (-3) 3 && x (-3) 14)
        clear * - r50722 b50723 b50724 b50725 b50726 b50727 g3 d50717 d49195 d49215
        omega
      have d50728 : (x (-4) 12).toNat = 1 := by
        have r50729 : (x (-4) 4).toNat ≤ (x (-4) 12).toNat := himp _ _ (hp4 (-4))
        have b50730 := hb (x (-4) 4)
        have b50731 := hb (x (-4) 12)
        clear * - r50729 b50730 b50731 d50721
        omega
      have d50732 : (x (-5) 13).toNat = 0 := by
        have r50733 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
        have e50734 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e50735 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b50736 := hb (x (-7) 3)
        have b50737 := hb (x (-6) 2)
        have b50738 := hb (x (-5) 13)
        have b50739 := hb (x (-4) 12)
        clear * - r50733 e50734 e50735 b50736 b50737 b50738 b50739 d50728
        omega
      have d50740 : (x (-5) 2 && x (-5) 13).toNat = 0 := by
        have r50741 := hand2 (x (-5) 2) (x (-5) 13)
        have b50742 := hb (x (-5) 13)
        have b50743 := hb (x (-5) 2 && x (-5) 13)
        clear * - r50741 b50742 b50743 d50732
        omega
      have d50744 : (x (-6) 2).toNat = 0 := by
        have r50745 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
        have e50746 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e50747 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b50748 := hb (x (-7) 3)
        have b50749 := hb (x (-6) 2)
        have b50750 := hb (x (-5) 13)
        have b50751 := hb (x (-4) 12)
        clear * - r50745 e50746 e50747 b50748 b50749 b50750 b50751 d50728 d50732
        omega
      have d50752 : (x (-6) 2 && x (-6) 13).toNat = 0 := by
        have r50753 := hand1 (x (-6) 2) (x (-6) 13)
        have b50754 := hb (x (-6) 2)
        have b50755 := hb (x (-6) 2 && x (-6) 13)
        clear * - r50753 b50754 b50755 d50744
        omega
      have d50756 : (x (-6) 2 && x (-6) 11).toNat = 0 := by
        have r50757 := hand1 (x (-6) 2) (x (-6) 11)
        have b50758 := hb (x (-6) 2)
        have b50759 := hb (x (-6) 2 && x (-6) 11)
        clear * - r50757 b50758 b50759 d50744
        omega
      have d50760 : (x (-5) 1 && x (-5) 14).toNat = 1 := by
        have r50761 : 1 ≤ (x (-4) 13).toNat + (x (-5) 1 && x (-5) 14).toNat + (x (-6) 2).toNat := hcov13 (-4)
        have b50762 := hb (x (-6) 2)
        have b50763 := hb (x (-4) 13)
        have b50764 := hb (x (-5) 1 && x (-5) 14)
        clear * - r50761 b50762 b50763 b50764 d50697 d50744
        omega
      have d50765 : (x (-5) 14).toNat = 1 := by
        have r50766 := hand2 (x (-5) 1) (x (-5) 14)
        have b50767 := hb (x (-5) 14)
        have b50768 := hb (x (-5) 1 && x (-5) 14)
        clear * - r50766 b50767 b50768 d50760
        omega
      have d50769 : (x (-6) 1).toNat = 0 := by
        have r50770 : (x (-5) 14).toNat + (x (-6) 1).toNat = 1 := hd14 (-5)
        have b50771 := hb (x (-6) 1)
        have b50772 := hb (x (-5) 14)
        clear * - r50770 b50771 b50772 d50765
        omega
      have d50773 : (x (-6) 1 && x (-6) 14).toNat = 0 := by
        have r50774 := hand1 (x (-6) 1) (x (-6) 14)
        have b50775 := hb (x (-6) 1)
        have b50776 := hb (x (-6) 1 && x (-6) 14)
        clear * - r50774 b50775 b50776 d50769
        omega
      have d50777 : (x (-7) 2).toNat = 1 := by
        have r50778 : 1 ≤ (x (-5) 13).toNat + (x (-6) 1 && x (-6) 14).toNat + (x (-7) 2).toNat := hcov13 (-5)
        have b50779 := hb (x (-7) 2)
        have b50780 := hb (x (-5) 13)
        have b50781 := hb (x (-6) 1 && x (-6) 14)
        clear * - r50778 b50779 b50780 b50781 d50732 d50773
        omega
      have d50782 : (x (-7) 14).toNat = 1 := by
        have r50783 : (x (-7) 2).toNat ≤ (x (-7) 14).toNat := himp _ _ (hp2 (-7))
        have b50784 := hb (x (-7) 2)
        have b50785 := hb (x (-7) 14)
        clear * - r50783 b50784 b50785 d50777
        omega
      have d50786 : (x (-8) 1).toNat = 0 := by
        have r50787 : (x (-7) 14).toNat + (x (-8) 1).toNat = 1 := hd14 (-7)
        have b50788 := hb (x (-8) 1)
        have b50789 := hb (x (-7) 14)
        clear * - r50787 b50788 b50789 d50782
        omega
      have d50790 : (x (-8) 1 && x (-8) 14).toNat = 0 := by
        have r50791 := hand1 (x (-8) 1) (x (-8) 14)
        have b50792 := hb (x (-8) 1)
        have b50793 := hb (x (-8) 1 && x (-8) 14)
        clear * - r50791 b50792 b50793 d50786
        omega
      have d50794 : (x (-8) 1 && x (-8) 12).toNat = 0 := by
        have r50795 := hand1 (x (-8) 1) (x (-8) 12)
        have b50796 := hb (x (-8) 1)
        have b50797 := hb (x (-8) 1 && x (-8) 12)
        clear * - r50795 b50796 b50797 d50786
        omega
      have d50798 : (x (-8) 13).toNat = 0 := by
        have r50799 : (x (-8) 13).toNat ≤ (x (-8) 1).toNat := himp _ _ (hp13 (-8))
        have b50800 := hb (x (-8) 1)
        have b50801 := hb (x (-8) 13)
        clear * - r50799 b50800 b50801 d50786
        omega
      have d50802 : (x (-8) 4 && x (-8) 13).toNat = 0 := by
        have r50803 := hand2 (x (-8) 4) (x (-8) 13)
        have b50804 := hb (x (-8) 13)
        have b50805 := hb (x (-8) 4 && x (-8) 13)
        clear * - r50803 b50804 b50805 d50798
        omega
      have d50806 : (x (-5) 12).toNat = 0 := by
        have r50807 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := hd12 (-5)
        have e50808 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
        have e50809 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
        have b50810 := hb (x (-8) 3)
        have b50811 := hb (x (-7) 2)
        have b50812 := hb (x (-6) 13)
        have b50813 := hb (x (-5) 12)
        clear * - r50807 e50808 e50809 b50810 b50811 b50812 b50813 d50777
        omega
      have d50814 : (x (-5) 1 && x (-5) 12).toNat = 0 := by
        have r50815 := hand2 (x (-5) 1) (x (-5) 12)
        have b50816 := hb (x (-5) 12)
        have b50817 := hb (x (-5) 1 && x (-5) 12)
        clear * - r50815 b50816 b50817 d50806
        omega
      have d50818 : (x (-7) 3).toNat = 0 := by
        have r50819 : (x (-4) 12).toNat + (x (-5) 1 && x (-5) 13).toNat + (x (-6) 2 && x (-6) 14).toNat + (x (-7) 3).toNat = 1 := hd12 (-4)
        have e50820 : (x (-5) 1 && x (-5) 13).toNat = (x (-5) 13).toNat := handr _ _ (fun h => hp13 (-5) (h))
        have e50821 : (x (-6) 2 && x (-6) 14).toNat = (x (-6) 2).toNat := handl _ _ (fun h => hp2 (-6) (h))
        have b50822 := hb (x (-7) 3)
        have b50823 := hb (x (-6) 2)
        have b50824 := hb (x (-5) 13)
        have b50825 := hb (x (-4) 12)
        clear * - r50819 e50820 e50821 b50822 b50823 b50824 b50825 d50728 d50732 d50744
        omega
      have d50826 : (x (-7) 3 && x (-7) 14).toNat = 0 := by
        have r50827 := hand1 (x (-7) 3) (x (-7) 14)
        have b50828 := hb (x (-7) 3)
        have b50829 := hb (x (-7) 3 && x (-7) 14)
        clear * - r50827 b50828 b50829 d50818
        omega
      have d50830 : (x (-7) 3 && x (-7) 12).toNat = 0 := by
        have r50831 := hand1 (x (-7) 3) (x (-7) 12)
        have b50832 := hb (x (-7) 3)
        have b50833 := hb (x (-7) 3 && x (-7) 12)
        clear * - r50831 b50832 b50833 d50818
        omega
      have d50834 : (x (-7) 11).toNat = 0 := by
        have r50835 : (x (-7) 11).toNat ≤ (x (-7) 3).toNat := himp _ _ (hp11 (-7))
        have b50836 := hb (x (-7) 3)
        have b50837 := hb (x (-7) 11)
        clear * - r50835 b50836 b50837 d50818
        omega
      have d50838 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
        have r50839 := hand2 (x (-1) 2) (x (-1) 12)
        have b50840 := hb (x (-1) 12)
        have b50841 := hb (x (-1) 2 && x (-1) 12)
        clear * - r50839 b50840 b50841 d50709
        omega
      have d50842 : (x (-2) 13).toNat = 0 := by
        have r50843 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
        have e50844 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e50845 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b50846 := hb (x (-4) 3)
        have b50847 := hb (x (-3) 2)
        have b50848 := hb (x (-2) 13)
        have b50849 := hb (x (-1) 12)
        clear * - r50843 e50844 e50845 b50846 b50847 b50848 b50849 d50709 d50680
        omega
      have d50850 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
        have r50851 := hand2 (x (-2) 3) (x (-2) 13)
        have b50852 := hb (x (-2) 13)
        have b50853 := hb (x (-2) 3 && x (-2) 13)
        clear * - r50851 b50852 b50853 d50842
        omega
      have d50854 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
        have r50855 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := hcov10 1
        have b50856 := hb (x (-4) 5)
        have b50857 := hb (x 1 10)
        have b50858 := hb (x 0 1 && x 0 11)
        have b50859 := hb (x (-1) 2 && x (-1) 12)
        have b50860 := hb (x (-2) 3 && x (-2) 13)
        have b50861 := hb (x (-3) 4 && x (-3) 14)
        clear * - r50855 b50856 b50857 b50858 b50859 b50860 b50861 g6 g12 d50838 d50850 d50701
        omega
      have d50862 : (x (-3) 4).toNat = 1 := by
        have r50863 := hand1 (x (-3) 4) (x (-3) 14)
        have b50864 := hb (x (-3) 4)
        have b50865 := hb (x (-3) 4 && x (-3) 14)
        clear * - r50863 b50864 b50865 d50854
        omega
      have d50866 : (x (-3) 12).toNat = 1 := by
        have r50867 : (x (-3) 4).toNat ≤ (x (-3) 12).toNat := himp _ _ (hp4 (-3))
        have b50868 := hb (x (-3) 4)
        have b50869 := hb (x (-3) 12)
        clear * - r50867 b50868 b50869 d50862
        omega
      have d50870 : (x (-5) 2).toNat = 0 := by
        have r50871 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
        have e50872 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e50873 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b50874 := hb (x (-6) 3)
        have b50875 := hb (x (-5) 2)
        have b50876 := hb (x (-4) 13)
        have b50877 := hb (x (-3) 12)
        clear * - r50871 e50872 e50873 b50874 b50875 b50876 b50877 d50866 d50697
        omega
      have d50878 : (x (-5) 10).toNat = 0 := by
        have r50879 : (x (-5) 10).toNat ≤ (x (-5) 2).toNat := himp _ _ (hp10 (-5))
        have b50880 := hb (x (-5) 2)
        have b50881 := hb (x (-5) 10)
        clear * - r50879 b50880 b50881 d50870
        omega
      have d50882 : (x (-5) 1 && x (-5) 10).toNat = 0 := by
        have r50883 := hand2 (x (-5) 1) (x (-5) 10)
        have b50884 := hb (x (-5) 10)
        have b50885 := hb (x (-5) 1 && x (-5) 10)
        clear * - r50883 b50884 b50885 d50878
        omega
      have d50886 : (x (-6) 3).toNat = 0 := by
        have r50887 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := hd12 (-3)
        have e50888 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
        have e50889 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
        have b50890 := hb (x (-6) 3)
        have b50891 := hb (x (-5) 2)
        have b50892 := hb (x (-4) 13)
        have b50893 := hb (x (-3) 12)
        clear * - r50887 e50888 e50889 b50890 b50891 b50892 b50893 d50866 d50697 d50870
        omega
      have d50894 : (x (-6) 3 && x (-6) 14).toNat = 0 := by
        have r50895 := hand1 (x (-6) 3) (x (-6) 14)
        have b50896 := hb (x (-6) 3)
        have b50897 := hb (x (-6) 3 && x (-6) 14)
        clear * - r50895 b50896 b50897 d50886
        omega
      have d50898 : (x (-7) 4).toNat = 1 := by
        have r50899 : 1 ≤ (x (-3) 11).toNat + (x (-4) 1 && x (-4) 12).toNat + (x (-5) 2 && x (-5) 13).toNat + (x (-6) 3 && x (-6) 14).toNat + (x (-7) 4).toNat := hcov11 (-3)
        have b50900 := hb (x (-7) 4)
        have b50901 := hb (x (-3) 11)
        have b50902 := hb (x (-4) 1 && x (-4) 12)
        have b50903 := hb (x (-5) 2 && x (-5) 13)
        have b50904 := hb (x (-6) 3 && x (-6) 14)
        clear * - r50899 b50900 b50901 b50902 b50903 b50904 d49223 d50693 d50740 d50894
        omega
      have d50905 : (x (-7) 12).toNat = 1 := by
        have r50906 : (x (-7) 4).toNat ≤ (x (-7) 12).toNat := himp _ _ (hp4 (-7))
        have b50907 := hb (x (-7) 4)
        have b50908 := hb (x (-7) 12)
        clear * - r50906 b50907 b50908 d50898
        omega
      have d50909 : (x (-9) 2).toNat = 0 := by
        have r50910 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
        have e50911 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
        have e50912 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
        have b50913 := hb (x (-10) 3)
        have b50914 := hb (x (-9) 2)
        have b50915 := hb (x (-8) 13)
        have b50916 := hb (x (-7) 12)
        clear * - r50910 e50911 e50912 b50913 b50914 b50915 b50916 d50905 d50798
        omega
      have d50917 : (x (-9) 2 && x (-9) 13).toNat = 0 := by
        have r50918 := hand1 (x (-9) 2) (x (-9) 13)
        have b50919 := hb (x (-9) 2)
        have b50920 := hb (x (-9) 2 && x (-9) 13)
        clear * - r50918 b50919 b50920 d50909
        omega
      have d50921 : (x (-7) 13).toNat = 1 := by
        have r50922 : 1 ≤ (x (-7) 13).toNat + (x (-8) 1 && x (-8) 14).toNat + (x (-9) 2).toNat := hcov13 (-7)
        have b50923 := hb (x (-9) 2)
        have b50924 := hb (x (-7) 13)
        have b50925 := hb (x (-8) 1 && x (-8) 14)
        clear * - r50922 b50923 b50924 b50925 d50790 d50909
        omega
      have d50926 : (x (-6) 12).toNat = 0 := by
        have r50927 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := hd12 (-6)
        have e50928 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e50929 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b50930 := hb (x (-9) 3)
        have b50931 := hb (x (-8) 2)
        have b50932 := hb (x (-7) 13)
        have b50933 := hb (x (-6) 12)
        clear * - r50927 e50928 e50929 b50930 b50931 b50932 b50933 d50921
        omega
      have d50934 : (x (-8) 2).toNat = 0 := by
        have r50935 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := hd12 (-6)
        have e50936 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e50937 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b50938 := hb (x (-9) 3)
        have b50939 := hb (x (-8) 2)
        have b50940 := hb (x (-7) 13)
        have b50941 := hb (x (-6) 12)
        clear * - r50935 e50936 e50937 b50938 b50939 b50940 b50941 d50926 d50921
        omega
      have d50942 : (x (-8) 10).toNat = 0 := by
        have r50943 : (x (-8) 10).toNat ≤ (x (-8) 2).toNat := himp _ _ (hp10 (-8))
        have b50944 := hb (x (-8) 2)
        have b50945 := hb (x (-8) 10)
        clear * - r50943 b50944 b50945 d50934
        omega
      have d50946 : (x (-9) 3).toNat = 0 := by
        have r50947 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := hd12 (-6)
        have e50948 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
        have e50949 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
        have b50950 := hb (x (-9) 3)
        have b50951 := hb (x (-8) 2)
        have b50952 := hb (x (-7) 13)
        have b50953 := hb (x (-6) 12)
        clear * - r50947 e50948 e50949 b50950 b50951 b50952 b50953 d50926 d50921 d50934
        omega
      have d50954 : (x (-9) 11).toNat = 0 := by
        have r50955 : (x (-9) 11).toNat ≤ (x (-9) 3).toNat := himp _ _ (hp11 (-9))
        have b50956 := hb (x (-9) 3)
        have b50957 := hb (x (-9) 11)
        clear * - r50955 b50956 b50957 d50946
        omega
      have d50958 : (x (-9) 1 && x (-9) 11).toNat = 0 := by
        have r50959 := hand2 (x (-9) 1) (x (-9) 11)
        have b50960 := hb (x (-9) 11)
        have b50961 := hb (x (-9) 1 && x (-9) 11)
        clear * - r50959 b50960 b50961 d50954
        omega
      have d50962 : (x (-10) 3).toNat = 0 := by
        have r50963 : (x (-7) 12).toNat + (x (-8) 1 && x (-8) 13).toNat + (x (-9) 2 && x (-9) 14).toNat + (x (-10) 3).toNat = 1 := hd12 (-7)
        have e50964 : (x (-8) 1 && x (-8) 13).toNat = (x (-8) 13).toNat := handr _ _ (fun h => hp13 (-8) (h))
        have e50965 : (x (-9) 2 && x (-9) 14).toNat = (x (-9) 2).toNat := handl _ _ (fun h => hp2 (-9) (h))
        have b50966 := hb (x (-10) 3)
        have b50967 := hb (x (-9) 2)
        have b50968 := hb (x (-8) 13)
        have b50969 := hb (x (-7) 12)
        clear * - r50963 e50964 e50965 b50966 b50967 b50968 b50969 d50905 d50798 d50909
        omega
      have d50970 : (x (-10) 3 && x (-10) 14).toNat = 0 := by
        have r50971 := hand1 (x (-10) 3) (x (-10) 14)
        have b50972 := hb (x (-10) 3)
        have b50973 := hb (x (-10) 3 && x (-10) 14)
        clear * - r50971 b50972 b50973 d50962
        omega
      have d50974 : (x (-11) 4).toNat = 1 := by
        have r50975 : 1 ≤ (x (-7) 11).toNat + (x (-8) 1 && x (-8) 12).toNat + (x (-9) 2 && x (-9) 13).toNat + (x (-10) 3 && x (-10) 14).toNat + (x (-11) 4).toNat := hcov11 (-7)
        have b50976 := hb (x (-11) 4)
        have b50977 := hb (x (-7) 11)
        have b50978 := hb (x (-8) 1 && x (-8) 12)
        have b50979 := hb (x (-9) 2 && x (-9) 13)
        have b50980 := hb (x (-10) 3 && x (-10) 14)
        clear * - r50975 b50976 b50977 b50978 b50979 b50980 d50834 d50794 d50917 d50970
        omega
      have d50981 : (x (-11) 12).toNat = 1 := by
        have r50982 : (x (-11) 4).toNat ≤ (x (-11) 12).toNat := himp _ _ (hp4 (-11))
        have b50983 := hb (x (-11) 4)
        have b50984 := hb (x (-11) 12)
        clear * - r50982 b50983 b50984 d50974
        omega
      have d50985 : (x (-12) 13).toNat = 0 := by
        have r50986 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := hd12 (-11)
        have e50987 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
        have e50988 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
        have b50989 := hb (x (-14) 3)
        have b50990 := hb (x (-13) 2)
        have b50991 := hb (x (-12) 13)
        have b50992 := hb (x (-11) 12)
        clear * - r50986 e50987 e50988 b50989 b50990 b50991 b50992 d50981
        omega
      have d50993 : (x (-13) 2).toNat = 0 := by
        have r50994 : (x (-11) 12).toNat + (x (-12) 1 && x (-12) 13).toNat + (x (-13) 2 && x (-13) 14).toNat + (x (-14) 3).toNat = 1 := hd12 (-11)
        have e50995 : (x (-12) 1 && x (-12) 13).toNat = (x (-12) 13).toNat := handr _ _ (fun h => hp13 (-12) (h))
        have e50996 : (x (-13) 2 && x (-13) 14).toNat = (x (-13) 2).toNat := handl _ _ (fun h => hp2 (-13) (h))
        have b50997 := hb (x (-14) 3)
        have b50998 := hb (x (-13) 2)
        have b50999 := hb (x (-12) 13)
        have b51000 := hb (x (-11) 12)
        clear * - r50994 e50995 e50996 b50997 b50998 b50999 b51000 d50981 d50985
        omega
      have d51001 : (x (-4) 3).toNat = 0 := by
        have r51002 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := hd12 (-1)
        have e51003 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
        have e51004 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
        have b51005 := hb (x (-4) 3)
        have b51006 := hb (x (-3) 2)
        have b51007 := hb (x (-2) 13)
        have b51008 := hb (x (-1) 12)
        clear * - r51002 e51003 e51004 b51005 b51006 b51007 b51008 d50709 d50842 d50680
        omega
      have d51009 : (x (-4) 11).toNat = 0 := by
        have r51010 : (x (-4) 11).toNat ≤ (x (-4) 3).toNat := himp _ _ (hp11 (-4))
        have b51011 := hb (x (-4) 3)
        have b51012 := hb (x (-4) 11)
        clear * - r51010 b51011 b51012 d51001
        omega
      have d51013 : (x (-8) 4).toNat = 1 := by
        have r51014 : 1 ≤ (x (-4) 11).toNat + (x (-5) 1 && x (-5) 12).toNat + (x (-6) 2 && x (-6) 13).toNat + (x (-7) 3 && x (-7) 14).toNat + (x (-8) 4).toNat := hcov11 (-4)
        have b51015 := hb (x (-8) 4)
        have b51016 := hb (x (-4) 11)
        have b51017 := hb (x (-5) 1 && x (-5) 12)
        have b51018 := hb (x (-6) 2 && x (-6) 13)
        have b51019 := hb (x (-7) 3 && x (-7) 14)
        clear * - r51014 b51015 b51016 b51017 b51018 b51019 d51009 d50814 d50752 d50826
        omega
      have d51020 : (x (-8) 12).toNat = 1 := by
        have r51021 : (x (-8) 4).toNat ≤ (x (-8) 12).toNat := himp _ _ (hp4 (-8))
        have b51022 := hb (x (-8) 4)
        have b51023 := hb (x (-8) 12)
        clear * - r51021 b51022 b51023 d51013
        omega
      have d51024 : (x (-9) 13).toNat = 0 := by
        have r51025 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := hd12 (-8)
        have e51026 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
        have e51027 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
        have b51028 := hb (x (-11) 3)
        have b51029 := hb (x (-10) 2)
        have b51030 := hb (x (-9) 13)
        have b51031 := hb (x (-8) 12)
        clear * - r51025 e51026 e51027 b51028 b51029 b51030 b51031 d51020
        omega
      have d51032 : (x (-9) 5).toNat = 0 := by
        have r51033 : (x (-9) 5).toNat ≤ (x (-9) 13).toNat := himp _ _ (hp5 (-9))
        have b51034 := hb (x (-9) 5)
        have b51035 := hb (x (-9) 13)
        clear * - r51033 b51034 b51035 d51024
        omega
      have d51036 : (x (-9) 5 && x (-9) 14).toNat = 0 := by
        have r51037 := hand1 (x (-9) 5) (x (-9) 14)
        have b51038 := hb (x (-9) 5)
        have b51039 := hb (x (-9) 5 && x (-9) 14)
        clear * - r51037 b51038 b51039 d51032
        omega
      have d51040 : (x (-10) 6).toNat = 1 := by
        have r51041 : 1 ≤ (x (-4) 9).toNat + (x (-5) 1 && x (-5) 10).toNat + (x (-6) 2 && x (-6) 11).toNat + (x (-7) 3 && x (-7) 12).toNat + (x (-8) 4 && x (-8) 13).toNat + (x (-9) 5 && x (-9) 14).toNat + (x (-10) 6).toNat := hcov9 (-4)
        have b51042 := hb (x (-10) 6)
        have b51043 := hb (x (-4) 9)
        have b51044 := hb (x (-5) 1 && x (-5) 10)
        have b51045 := hb (x (-6) 2 && x (-6) 11)
        have b51046 := hb (x (-7) 3 && x (-7) 12)
        have b51047 := hb (x (-8) 4 && x (-8) 13)
        have b51048 := hb (x (-9) 5 && x (-9) 14)
        clear * - r51041 b51042 b51043 b51044 b51045 b51046 b51047 b51048 d50705 d50882 d50756 d50830 d50802 d51036
        omega
      have d51049 : (x (-10) 14).toNat = 1 := by
        have r51050 : (x (-10) 6).toNat ≤ (x (-10) 14).toNat := himp _ _ (hp6 (-10))
        have b51051 := hb (x (-10) 6)
        have b51052 := hb (x (-10) 14)
        clear * - r51050 b51051 b51052 d51040
        omega
      have d51053 : (x (-11) 1).toNat = 0 := by
        have r51054 : (x (-10) 14).toNat + (x (-11) 1).toNat = 1 := hd14 (-10)
        have b51055 := hb (x (-11) 1)
        have b51056 := hb (x (-10) 14)
        clear * - r51054 b51055 b51056 d51049
        omega
      have d51057 : (x (-11) 13).toNat = 0 := by
        have r51058 : (x (-11) 13).toNat ≤ (x (-11) 1).toNat := himp _ _ (hp13 (-11))
        have b51059 := hb (x (-11) 1)
        have b51060 := hb (x (-11) 13)
        clear * - r51058 b51059 b51060 d51053
        omega
      have d51061 : (x (-11) 3 && x (-11) 13).toNat = 0 := by
        have r51062 := hand2 (x (-11) 3) (x (-11) 13)
        have b51063 := hb (x (-11) 13)
        have b51064 := hb (x (-11) 3 && x (-11) 13)
        clear * - r51062 b51063 b51064 d51057
        omega
      have d51065 : (x (-12) 1 && x (-12) 14).toNat = 1 := by
        have r51066 : 1 ≤ (x (-11) 13).toNat + (x (-12) 1 && x (-12) 14).toNat + (x (-13) 2).toNat := hcov13 (-11)
        have b51067 := hb (x (-13) 2)
        have b51068 := hb (x (-11) 13)
        have b51069 := hb (x (-12) 1 && x (-12) 14)
        clear * - r51066 b51067 b51068 b51069 d51057 d50993
        omega
      have d51070 : (x (-12) 14).toNat = 1 := by
        have r51071 := hand2 (x (-12) 1) (x (-12) 14)
        have b51072 := hb (x (-12) 14)
        have b51073 := hb (x (-12) 1 && x (-12) 14)
        clear * - r51071 b51072 b51073 d51065
        omega
      have d51074 : (x (-13) 1).toNat = 0 := by
        have r51075 : (x (-12) 14).toNat + (x (-13) 1).toNat = 1 := hd14 (-12)
        have b51076 := hb (x (-13) 1)
        have b51077 := hb (x (-12) 14)
        clear * - r51075 b51076 b51077 d51070
        omega
      have d51078 : (x (-13) 1 && x (-13) 14).toNat = 0 := by
        have r51079 := hand1 (x (-13) 1) (x (-13) 14)
        have b51080 := hb (x (-13) 1)
        have b51081 := hb (x (-13) 1 && x (-13) 14)
        clear * - r51079 b51080 b51081 d51074
        omega
      have d51082 : (x (-14) 2).toNat = 1 := by
        have r51083 : 1 ≤ (x (-12) 13).toNat + (x (-13) 1 && x (-13) 14).toNat + (x (-14) 2).toNat := hcov13 (-12)
        have b51084 := hb (x (-14) 2)
        have b51085 := hb (x (-12) 13)
        have b51086 := hb (x (-13) 1 && x (-13) 14)
        clear * - r51083 b51084 b51085 b51086 d50985 d51078
        omega
      have d51087 : (x (-12) 12).toNat = 0 := by
        have r51088 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := hd12 (-12)
        have e51089 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
        have e51090 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
        have b51091 := hb (x (-15) 3)
        have b51092 := hb (x (-14) 2)
        have b51093 := hb (x (-13) 13)
        have b51094 := hb (x (-12) 12)
        clear * - r51088 e51089 e51090 b51091 b51092 b51093 b51094 d51082
        omega
      have d51095 : (x (-12) 4).toNat = 0 := by
        have r51096 : (x (-12) 4).toNat ≤ (x (-12) 12).toNat := himp _ _ (hp4 (-12))
        have b51097 := hb (x (-12) 4)
        have b51098 := hb (x (-12) 12)
        clear * - r51096 b51097 b51098 d51087
        omega
      have d51099 : (x (-12) 4 && x (-12) 14).toNat = 0 := by
        have r51100 := hand1 (x (-12) 4) (x (-12) 14)
        have b51101 := hb (x (-12) 4)
        have b51102 := hb (x (-12) 4 && x (-12) 14)
        clear * - r51100 b51101 b51102 d51095
        omega
      have d51103 : (x (-13) 13).toNat = 0 := by
        have r51104 : (x (-12) 12).toNat + (x (-13) 1 && x (-13) 13).toNat + (x (-14) 2 && x (-14) 14).toNat + (x (-15) 3).toNat = 1 := hd12 (-12)
        have e51105 : (x (-13) 1 && x (-13) 13).toNat = (x (-13) 13).toNat := handr _ _ (fun h => hp13 (-13) (h))
        have e51106 : (x (-14) 2 && x (-14) 14).toNat = (x (-14) 2).toNat := handl _ _ (fun h => hp2 (-14) (h))
        have b51107 := hb (x (-15) 3)
        have b51108 := hb (x (-14) 2)
        have b51109 := hb (x (-13) 13)
        have b51110 := hb (x (-12) 12)
        clear * - r51104 e51105 e51106 b51107 b51108 b51109 b51110 d51087 d51082
        omega
      have d51111 : (x (-13) 5).toNat = 0 := by
        have r51112 : (x (-13) 5).toNat ≤ (x (-13) 13).toNat := himp _ _ (hp5 (-13))
        have b51113 := hb (x (-13) 5)
        have b51114 := hb (x (-13) 13)
        clear * - r51112 b51113 b51114 d51103
        omega
      have d51115 : (x (-10) 2 && x (-10) 12).toNat = 1 := by
        have r51116 : 1 ≤ (x (-8) 10).toNat + (x (-9) 1 && x (-9) 11).toNat + (x (-10) 2 && x (-10) 12).toNat + (x (-11) 3 && x (-11) 13).toNat + (x (-12) 4 && x (-12) 14).toNat + (x (-13) 5).toNat := hcov10 (-8)
        have b51117 := hb (x (-13) 5)
        have b51118 := hb (x (-8) 10)
        have b51119 := hb (x (-9) 1 && x (-9) 11)
        have b51120 := hb (x (-10) 2 && x (-10) 12)
        have b51121 := hb (x (-11) 3 && x (-11) 13)
        have b51122 := hb (x (-12) 4 && x (-12) 14)
        clear * - r51116 b51117 b51118 b51119 b51120 b51121 b51122 d50942 d50958 d51061 d51099 d51111
        omega
      have d51123 : (x (-10) 2).toNat = 1 := by
        have r51124 := hand1 (x (-10) 2) (x (-10) 12)
        have b51125 := hb (x (-10) 2)
        have b51126 := hb (x (-10) 2 && x (-10) 12)
        clear * - r51124 b51125 b51126 d51115
        omega
      have r51127 : (x (-8) 12).toNat + (x (-9) 1 && x (-9) 13).toNat + (x (-10) 2 && x (-10) 14).toNat + (x (-11) 3).toNat = 1 := hd12 (-8)
      have e51128 : (x (-9) 1 && x (-9) 13).toNat = (x (-9) 13).toNat := handr _ _ (fun h => hp13 (-9) (h))
      have e51129 : (x (-10) 2 && x (-10) 14).toNat = (x (-10) 2).toNat := handl _ _ (fun h => hp2 (-10) (h))
      have b51130 := hb (x (-11) 3)
      have b51131 := hb (x (-10) 2)
      have b51132 := hb (x (-9) 13)
      have b51133 := hb (x (-8) 12)
      linarith only [r51127, e51128, e51129, b51130, b51131, b51132, b51133, d51020, d51024, d51123]
  · have f51134 : (x 0 5).toNat = 1 := by rw [h49279]; rfl
    have d51135 : (x 0 13).toNat = 1 := by
      have r51136 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
      have b51137 := hb (x 0 5)
      have b51138 := hb (x 0 13)
      clear * - r51136 b51137 b51138 f51134
      omega
    have d51139 : (x 1 12).toNat = 0 := by
      have r51140 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
      have e51141 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e51142 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b51143 := hb (x (-2) 3)
      have b51144 := hb (x (-1) 2)
      have b51145 := hb (x 0 13)
      have b51146 := hb (x 1 12)
      clear * - r51140 e51141 e51142 b51143 b51144 b51145 b51146 d51135
      omega
    have d51147 : (x (-1) 2).toNat = 0 := by
      have r51148 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := hd12 1
      have e51149 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e51150 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b51151 := hb (x (-2) 3)
      have b51152 := hb (x (-1) 2)
      have b51153 := hb (x 0 13)
      have b51154 := hb (x 1 12)
      clear * - r51148 e51149 e51150 b51151 b51152 b51153 b51154 d51139 d51135
      omega
    have d51155 : (x 1 13).toNat = 1 := by
      have r51156 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := hcov13 1
      have b51157 := hb (x (-1) 2)
      have b51158 := hb (x 1 13)
      have b51159 := hb (x 0 1 && x 0 14)
      clear * - r51156 b51157 b51158 b51159 g19 d51147
      omega
    have d51160 : (x 1 1).toNat = 1 := by
      have r51161 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
      have b51162 := hb (x 1 1)
      have b51163 := hb (x 1 13)
      clear * - r51161 b51162 b51163 d51155
      omega
    have d51164 : (x 2 14).toNat = 0 := by
      have r51165 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
      have b51166 := hb (x 1 1)
      have b51167 := hb (x 2 14)
      clear * - r51165 b51166 b51167 d51160
      omega
    have d51168 : (x 2 1 && x 2 14).toNat = 0 := by
      have r51169 := hand2 (x 2 1) (x 2 14)
      have b51170 := hb (x 2 14)
      have b51171 := hb (x 2 1 && x 2 14)
      clear * - r51169 b51170 b51171 d51164
      omega
    have d51172 : (x 3 13).toNat = 1 := by
      have r51173 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
      have b51174 := hb (x 1 2)
      have b51175 := hb (x 3 13)
      have b51176 := hb (x 2 1 && x 2 14)
      clear * - r51173 b51174 b51175 b51176 d51168 g4
      omega
    have d51177 : (x 3 1).toNat = 1 := by
      have r51178 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
      have b51179 := hb (x 3 1)
      have b51180 := hb (x 3 13)
      clear * - r51178 b51179 b51180 d51172
      omega
    have d51181 : (x 4 14).toNat = 0 := by
      have r51182 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
      have b51183 := hb (x 3 1)
      have b51184 := hb (x 4 14)
      clear * - r51182 b51183 b51184 d51177
      omega
    have d51185 : (x 4 1 && x 4 14).toNat = 0 := by
      have r51186 := hand2 (x 4 1) (x 4 14)
      have b51187 := hb (x 4 14)
      have b51188 := hb (x 4 1 && x 4 14)
      clear * - r51186 b51187 b51188 d51181
      omega
    have d51189 : (x 5 13).toNat = 1 := by
      have r51190 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
      have b51191 := hb (x 3 2)
      have b51192 := hb (x 5 13)
      have b51193 := hb (x 4 1 && x 4 14)
      clear * - r51190 b51191 b51192 b51193 d51185 g7
      omega
    have d51194 : (x 5 1).toNat = 1 := by
      have r51195 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
      have b51196 := hb (x 5 1)
      have b51197 := hb (x 5 13)
      clear * - r51195 b51196 b51197 d51189
      omega
    have d51198 : (x 6 14).toNat = 0 := by
      have r51199 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
      have b51200 := hb (x 5 1)
      have b51201 := hb (x 6 14)
      clear * - r51199 b51200 b51201 d51194
      omega
    have d51202 : (x 6 1 && x 6 14).toNat = 0 := by
      have r51203 := hand2 (x 6 1) (x 6 14)
      have b51204 := hb (x 6 14)
      have b51205 := hb (x 6 1 && x 6 14)
      clear * - r51203 b51204 b51205 d51198
      omega
    have d51206 : (x 6 2).toNat = 0 := by
      have r51207 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
      have b51208 := hb (x 6 2)
      have b51209 := hb (x 6 14)
      clear * - r51207 b51208 b51209 d51198
      omega
    have d51210 : (x 6 12).toNat = 0 := by
      have r51211 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e51212 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e51213 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b51214 := hb (x 3 3)
      have b51215 := hb (x 4 2)
      have b51216 := hb (x 5 13)
      have b51217 := hb (x 6 12)
      clear * - r51211 e51212 e51213 b51214 b51215 b51216 b51217 d51189
      omega
    have d51218 : (x 4 2).toNat = 0 := by
      have r51219 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := hd12 6
      have e51220 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e51221 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b51222 := hb (x 3 3)
      have b51223 := hb (x 4 2)
      have b51224 := hb (x 5 13)
      have b51225 := hb (x 6 12)
      clear * - r51219 e51220 e51221 b51222 b51223 b51224 b51225 d51210 d51189
      omega
    have d51226 : (x 4 12).toNat = 0 := by
      have r51227 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
      have e51228 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e51229 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b51230 := hb (x 1 3)
      have b51231 := hb (x 2 2)
      have b51232 := hb (x 3 13)
      have b51233 := hb (x 4 12)
      clear * - r51227 e51228 e51229 b51230 b51231 b51232 b51233 d51172
      omega
    have d51234 : (x 2 2).toNat = 0 := by
      have r51235 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := hd12 4
      have e51236 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e51237 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b51238 := hb (x 1 3)
      have b51239 := hb (x 2 2)
      have b51240 := hb (x 3 13)
      have b51241 := hb (x 4 12)
      clear * - r51235 e51236 e51237 b51238 b51239 b51240 b51241 d51226 d51172
      omega
    have d51242 : (x 4 13).toNat = 1 := by
      have r51243 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
      have b51244 := hb (x 2 2)
      have b51245 := hb (x 4 13)
      have b51246 := hb (x 3 1 && x 3 14)
      clear * - r51243 b51244 b51245 b51246 g20 d51234
      omega
    have d51247 : (x 4 1).toNat = 1 := by
      have r51248 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
      have b51249 := hb (x 4 1)
      have b51250 := hb (x 4 13)
      clear * - r51248 b51249 b51250 d51242
      omega
    have d51251 : (x 5 14).toNat = 0 := by
      have r51252 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
      have b51253 := hb (x 4 1)
      have b51254 := hb (x 5 14)
      clear * - r51252 b51253 b51254 d51247
      omega
    have d51255 : (x 5 1 && x 5 14).toNat = 0 := by
      have r51256 := hand2 (x 5 1) (x 5 14)
      have b51257 := hb (x 5 14)
      have b51258 := hb (x 5 1 && x 5 14)
      clear * - r51256 b51257 b51258 d51251
      omega
    have d51259 : (x 6 13).toNat = 1 := by
      have r51260 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
      have b51261 := hb (x 4 2)
      have b51262 := hb (x 6 13)
      have b51263 := hb (x 5 1 && x 5 14)
      clear * - r51260 b51261 b51262 b51263 d51255 d51218
      omega
    have d51264 : (x 6 1).toNat = 1 := by
      have r51265 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
      have b51266 := hb (x 6 1)
      have b51267 := hb (x 6 13)
      clear * - r51265 b51266 b51267 d51259
      omega
    have d51268 : (x 7 14).toNat = 0 := by
      have r51269 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
      have b51270 := hb (x 6 1)
      have b51271 := hb (x 7 14)
      clear * - r51269 b51270 b51271 d51264
      omega
    have d51272 : (x 7 1 && x 7 14).toNat = 0 := by
      have r51273 := hand2 (x 7 1) (x 7 14)
      have b51274 := hb (x 7 14)
      have b51275 := hb (x 7 1 && x 7 14)
      clear * - r51273 b51274 b51275 d51268
      omega
    have d51276 : (x 8 13).toNat = 1 := by
      have r51277 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
      have b51278 := hb (x 6 2)
      have b51279 := hb (x 8 13)
      have b51280 := hb (x 7 1 && x 7 14)
      clear * - r51277 b51278 b51279 b51280 d51272 d51206
      omega
    have d51281 : (x 8 1).toNat = 1 := by
      have r51282 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
      have b51283 := hb (x 8 1)
      have b51284 := hb (x 8 13)
      clear * - r51282 b51283 b51284 d51276
      omega
    have d51285 : (x 9 14).toNat = 0 := by
      have r51286 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
      have b51287 := hb (x 8 1)
      have b51288 := hb (x 9 14)
      clear * - r51286 b51287 b51288 d51281
      omega
    have d51289 : (x 9 1 && x 9 14).toNat = 0 := by
      have r51290 := hand2 (x 9 1) (x 9 14)
      have b51291 := hb (x 9 14)
      have b51292 := hb (x 9 1 && x 9 14)
      clear * - r51290 b51291 b51292 d51285
      omega
    have d51293 : (x 9 2).toNat = 0 := by
      have r51294 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
      have b51295 := hb (x 9 2)
      have b51296 := hb (x 9 14)
      clear * - r51294 b51295 b51296 d51285
      omega
    have d51297 : (x 9 12).toNat = 0 := by
      have r51298 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
      have e51299 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e51300 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b51301 := hb (x 6 3)
      have b51302 := hb (x 7 2)
      have b51303 := hb (x 8 13)
      have b51304 := hb (x 9 12)
      clear * - r51298 e51299 e51300 b51301 b51302 b51303 b51304 d51276
      omega
    have d51305 : (x 7 2).toNat = 0 := by
      have r51306 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := hd12 9
      have e51307 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e51308 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b51309 := hb (x 6 3)
      have b51310 := hb (x 7 2)
      have b51311 := hb (x 8 13)
      have b51312 := hb (x 9 12)
      clear * - r51306 e51307 e51308 b51309 b51310 b51311 b51312 d51297 d51276
      omega
    have d51313 : (x 7 12).toNat = 0 := by
      have r51314 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
      have e51315 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e51316 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b51317 := hb (x 4 3)
      have b51318 := hb (x 5 2)
      have b51319 := hb (x 6 13)
      have b51320 := hb (x 7 12)
      clear * - r51314 e51315 e51316 b51317 b51318 b51319 b51320 d51259
      omega
    have d51321 : (x 5 2).toNat = 0 := by
      have r51322 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := hd12 7
      have e51323 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e51324 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b51325 := hb (x 4 3)
      have b51326 := hb (x 5 2)
      have b51327 := hb (x 6 13)
      have b51328 := hb (x 7 12)
      clear * - r51322 e51323 e51324 b51325 b51326 b51327 b51328 d51313 d51259
      omega
    have d51329 : (x 7 13).toNat = 1 := by
      have r51330 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
      have b51331 := hb (x 5 2)
      have b51332 := hb (x 7 13)
      have b51333 := hb (x 6 1 && x 6 14)
      clear * - r51330 b51331 b51332 b51333 d51202 d51321
      omega
    have d51334 : (x 7 1).toNat = 1 := by
      have r51335 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
      have b51336 := hb (x 7 1)
      have b51337 := hb (x 7 13)
      clear * - r51335 b51336 b51337 d51329
      omega
    have d51338 : (x 8 14).toNat = 0 := by
      have r51339 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
      have b51340 := hb (x 7 1)
      have b51341 := hb (x 8 14)
      clear * - r51339 b51340 b51341 d51334
      omega
    have d51342 : (x 8 1 && x 8 14).toNat = 0 := by
      have r51343 := hand2 (x 8 1) (x 8 14)
      have b51344 := hb (x 8 14)
      have b51345 := hb (x 8 1 && x 8 14)
      clear * - r51343 b51344 b51345 d51338
      omega
    have d51346 : (x 9 13).toNat = 1 := by
      have r51347 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
      have b51348 := hb (x 7 2)
      have b51349 := hb (x 9 13)
      have b51350 := hb (x 8 1 && x 8 14)
      clear * - r51347 b51348 b51349 b51350 d51342 d51305
      omega
    have d51351 : (x 9 1).toNat = 1 := by
      have r51352 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
      have b51353 := hb (x 9 1)
      have b51354 := hb (x 9 13)
      clear * - r51352 b51353 b51354 d51346
      omega
    have d51355 : (x 10 14).toNat = 0 := by
      have r51356 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
      have b51357 := hb (x 9 1)
      have b51358 := hb (x 10 14)
      clear * - r51356 b51357 b51358 d51351
      omega
    have d51359 : (x 10 1 && x 10 14).toNat = 0 := by
      have r51360 := hand2 (x 10 1) (x 10 14)
      have b51361 := hb (x 10 14)
      have b51362 := hb (x 10 1 && x 10 14)
      clear * - r51360 b51361 b51362 d51355
      omega
    have d51363 : (x 11 13).toNat = 1 := by
      have r51364 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
      have b51365 := hb (x 9 2)
      have b51366 := hb (x 11 13)
      have b51367 := hb (x 10 1 && x 10 14)
      clear * - r51364 b51365 b51366 b51367 d51359 d51293
      omega
    have d51368 : (x 11 1).toNat = 1 := by
      have r51369 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
      have b51370 := hb (x 11 1)
      have b51371 := hb (x 11 13)
      clear * - r51369 b51370 b51371 d51363
      omega
    have d51372 : (x 12 14).toNat = 0 := by
      have r51373 : (x 12 14).toNat + (x 11 1).toNat = 1 := hd14 12
      have b51374 := hb (x 11 1)
      have b51375 := hb (x 12 14)
      clear * - r51373 b51374 b51375 d51368
      omega
    have d51376 : (x 12 1 && x 12 14).toNat = 0 := by
      have r51377 := hand2 (x 12 1) (x 12 14)
      have b51378 := hb (x 12 14)
      have b51379 := hb (x 12 1 && x 12 14)
      clear * - r51377 b51378 b51379 d51372
      omega
    have d51380 : (x 12 2).toNat = 0 := by
      have r51381 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
      have b51382 := hb (x 12 2)
      have b51383 := hb (x 12 14)
      clear * - r51381 b51382 b51383 d51372
      omega
    have d51384 : (x 12 12).toNat = 0 := by
      have r51385 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
      have e51386 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e51387 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b51388 := hb (x 9 3)
      have b51389 := hb (x 10 2)
      have b51390 := hb (x 11 13)
      have b51391 := hb (x 12 12)
      clear * - r51385 e51386 e51387 b51388 b51389 b51390 b51391 d51363
      omega
    have d51392 : (x 10 2).toNat = 0 := by
      have r51393 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := hd12 12
      have e51394 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e51395 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b51396 := hb (x 9 3)
      have b51397 := hb (x 10 2)
      have b51398 := hb (x 11 13)
      have b51399 := hb (x 12 12)
      clear * - r51393 e51394 e51395 b51396 b51397 b51398 b51399 d51384 d51363
      omega
    have d51400 : (x 10 12).toNat = 0 := by
      have r51401 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
      have e51402 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e51403 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b51404 := hb (x 7 3)
      have b51405 := hb (x 8 2)
      have b51406 := hb (x 9 13)
      have b51407 := hb (x 10 12)
      clear * - r51401 e51402 e51403 b51404 b51405 b51406 b51407 d51346
      omega
    have d51408 : (x 8 2).toNat = 0 := by
      have r51409 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := hd12 10
      have e51410 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e51411 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b51412 := hb (x 7 3)
      have b51413 := hb (x 8 2)
      have b51414 := hb (x 9 13)
      have b51415 := hb (x 10 12)
      clear * - r51409 e51410 e51411 b51412 b51413 b51414 b51415 d51400 d51346
      omega
    have d51416 : (x 10 13).toNat = 1 := by
      have r51417 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
      have b51418 := hb (x 8 2)
      have b51419 := hb (x 10 13)
      have b51420 := hb (x 9 1 && x 9 14)
      clear * - r51417 b51418 b51419 b51420 d51289 d51408
      omega
    have d51421 : (x 10 1).toNat = 1 := by
      have r51422 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
      have b51423 := hb (x 10 1)
      have b51424 := hb (x 10 13)
      clear * - r51422 b51423 b51424 d51416
      omega
    have d51425 : (x 11 14).toNat = 0 := by
      have r51426 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
      have b51427 := hb (x 10 1)
      have b51428 := hb (x 11 14)
      clear * - r51426 b51427 b51428 d51421
      omega
    have d51429 : (x 11 1 && x 11 14).toNat = 0 := by
      have r51430 := hand2 (x 11 1) (x 11 14)
      have b51431 := hb (x 11 14)
      have b51432 := hb (x 11 1 && x 11 14)
      clear * - r51430 b51431 b51432 d51425
      omega
    have d51433 : (x 12 13).toNat = 1 := by
      have r51434 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
      have b51435 := hb (x 10 2)
      have b51436 := hb (x 12 13)
      have b51437 := hb (x 11 1 && x 11 14)
      clear * - r51434 b51435 b51436 b51437 d51429 d51392
      omega
    have d51438 : (x 12 1).toNat = 1 := by
      have r51439 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
      have b51440 := hb (x 12 1)
      have b51441 := hb (x 12 13)
      clear * - r51439 b51440 b51441 d51433
      omega
    have d51442 : (x 13 14).toNat = 0 := by
      have r51443 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
      have b51444 := hb (x 12 1)
      have b51445 := hb (x 13 14)
      clear * - r51443 b51444 b51445 d51438
      omega
    have d51446 : (x 13 1 && x 13 14).toNat = 0 := by
      have r51447 := hand2 (x 13 1) (x 13 14)
      have b51448 := hb (x 13 14)
      have b51449 := hb (x 13 1 && x 13 14)
      clear * - r51447 b51448 b51449 d51442
      omega
    have d51450 : (x 14 13).toNat = 1 := by
      have r51451 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
      have b51452 := hb (x 12 2)
      have b51453 := hb (x 14 13)
      have b51454 := hb (x 13 1 && x 13 14)
      clear * - r51451 b51452 b51453 b51454 d51446 d51380
      omega
    have d51455 : (x 14 1).toNat = 1 := by
      have r51456 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
      have b51457 := hb (x 14 1)
      have b51458 := hb (x 14 13)
      clear * - r51456 b51457 b51458 d51450
      omega
    have d51459 : (x 15 14).toNat = 0 := by
      have r51460 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
      have b51461 := hb (x 14 1)
      have b51462 := hb (x 15 14)
      clear * - r51460 b51461 b51462 d51455
      omega
    have d51463 : (x 15 1 && x 15 14).toNat = 0 := by
      have r51464 := hand2 (x 15 1) (x 15 14)
      have b51465 := hb (x 15 14)
      have b51466 := hb (x 15 1 && x 15 14)
      clear * - r51464 b51465 b51466 d51459
      omega
    have d51467 : (x 15 2).toNat = 0 := by
      have r51468 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
      have b51469 := hb (x 15 2)
      have b51470 := hb (x 15 14)
      clear * - r51468 b51469 b51470 d51459
      omega
    have d51471 : (x 15 2 && x 15 13).toNat = 0 := by
      have r51472 := hand1 (x 15 2) (x 15 13)
      have b51473 := hb (x 15 2)
      have b51474 := hb (x 15 2 && x 15 13)
      clear * - r51472 b51473 b51474 d51467
      omega
    have d51475 : (x 15 12).toNat = 0 := by
      have r51476 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
      have e51477 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e51478 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b51479 := hb (x 12 3)
      have b51480 := hb (x 13 2)
      have b51481 := hb (x 14 13)
      have b51482 := hb (x 15 12)
      clear * - r51476 e51477 e51478 b51479 b51480 b51481 b51482 d51450
      omega
    have d51483 : (x 13 2).toNat = 0 := by
      have r51484 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := hd12 15
      have e51485 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e51486 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b51487 := hb (x 12 3)
      have b51488 := hb (x 13 2)
      have b51489 := hb (x 14 13)
      have b51490 := hb (x 15 12)
      clear * - r51484 e51485 e51486 b51487 b51488 b51489 b51490 d51475 d51450
      omega
    have d51491 : (x 13 12).toNat = 0 := by
      have r51492 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
      have e51493 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e51494 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b51495 := hb (x 10 3)
      have b51496 := hb (x 11 2)
      have b51497 := hb (x 12 13)
      have b51498 := hb (x 13 12)
      clear * - r51492 e51493 e51494 b51495 b51496 b51497 b51498 d51433
      omega
    have d51499 : (x 13 4).toNat = 0 := by
      have r51500 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
      have b51501 := hb (x 13 4)
      have b51502 := hb (x 13 12)
      clear * - r51500 b51501 b51502 d51491
      omega
    have d51503 : (x 11 2).toNat = 0 := by
      have r51504 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
      have e51505 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e51506 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b51507 := hb (x 10 3)
      have b51508 := hb (x 11 2)
      have b51509 := hb (x 12 13)
      have b51510 := hb (x 13 12)
      clear * - r51504 e51505 e51506 b51507 b51508 b51509 b51510 d51491 d51433
      omega
    have d51511 : (x 13 13).toNat = 1 := by
      have r51512 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
      have b51513 := hb (x 11 2)
      have b51514 := hb (x 13 13)
      have b51515 := hb (x 12 1 && x 12 14)
      clear * - r51512 b51513 b51514 b51515 d51376 d51503
      omega
    have d51516 : (x 13 1).toNat = 1 := by
      have r51517 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
      have b51518 := hb (x 13 1)
      have b51519 := hb (x 13 13)
      clear * - r51517 b51518 b51519 d51511
      omega
    have d51520 : (x 14 14).toNat = 0 := by
      have r51521 : (x 14 14).toNat + (x 13 1).toNat = 1 := hd14 14
      have b51522 := hb (x 13 1)
      have b51523 := hb (x 14 14)
      clear * - r51521 b51522 b51523 d51516
      omega
    have d51524 : (x 14 1 && x 14 14).toNat = 0 := by
      have r51525 := hand2 (x 14 1) (x 14 14)
      have b51526 := hb (x 14 14)
      have b51527 := hb (x 14 1 && x 14 14)
      clear * - r51525 b51526 b51527 d51520
      omega
    have d51528 : (x 15 13).toNat = 1 := by
      have r51529 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
      have b51530 := hb (x 13 2)
      have b51531 := hb (x 15 13)
      have b51532 := hb (x 14 1 && x 14 14)
      clear * - r51529 b51530 b51531 b51532 d51524 d51483
      omega
    have d51533 : (x 15 1).toNat = 1 := by
      have r51534 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
      have b51535 := hb (x 15 1)
      have b51536 := hb (x 15 13)
      clear * - r51534 b51535 b51536 d51528
      omega
    have d51537 : (x 16 14).toNat = 0 := by
      have r51538 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
      have b51539 := hb (x 15 1)
      have b51540 := hb (x 16 14)
      clear * - r51538 b51539 b51540 d51533
      omega
    have d51541 : (x 16 1 && x 16 14).toNat = 0 := by
      have r51542 := hand2 (x 16 1) (x 16 14)
      have b51543 := hb (x 16 14)
      have b51544 := hb (x 16 1 && x 16 14)
      clear * - r51542 b51543 b51544 d51537
      omega
    have d51545 : (x 17 13).toNat = 1 := by
      have r51546 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
      have b51547 := hb (x 15 2)
      have b51548 := hb (x 17 13)
      have b51549 := hb (x 16 1 && x 16 14)
      clear * - r51546 b51547 b51548 b51549 d51541 d51467
      omega
    have d51550 : (x 17 1).toNat = 1 := by
      have r51551 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
      have b51552 := hb (x 17 1)
      have b51553 := hb (x 17 13)
      clear * - r51551 b51552 b51553 d51545
      omega
    have d51554 : (x 18 14).toNat = 0 := by
      have r51555 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
      have b51556 := hb (x 17 1)
      have b51557 := hb (x 18 14)
      clear * - r51555 b51556 b51557 d51550
      omega
    have d51558 : (x 18 1 && x 18 14).toNat = 0 := by
      have r51559 := hand2 (x 18 1) (x 18 14)
      have b51560 := hb (x 18 14)
      have b51561 := hb (x 18 1 && x 18 14)
      clear * - r51559 b51560 b51561 d51554
      omega
    have d51562 : (x 18 2).toNat = 0 := by
      have r51563 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
      have b51564 := hb (x 18 2)
      have b51565 := hb (x 18 14)
      clear * - r51563 b51564 b51565 d51554
      omega
    have d51566 : (x 18 12).toNat = 0 := by
      have r51567 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
      have e51568 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e51569 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b51570 := hb (x 15 3)
      have b51571 := hb (x 16 2)
      have b51572 := hb (x 17 13)
      have b51573 := hb (x 18 12)
      clear * - r51567 e51568 e51569 b51570 b51571 b51572 b51573 d51545
      omega
    have d51574 : (x 16 2).toNat = 0 := by
      have r51575 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := hd12 18
      have e51576 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e51577 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b51578 := hb (x 15 3)
      have b51579 := hb (x 16 2)
      have b51580 := hb (x 17 13)
      have b51581 := hb (x 18 12)
      clear * - r51575 e51576 e51577 b51578 b51579 b51580 b51581 d51566 d51545
      omega
    have d51582 : (x 16 12).toNat = 0 := by
      have r51583 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
      have e51584 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e51585 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b51586 := hb (x 13 3)
      have b51587 := hb (x 14 2)
      have b51588 := hb (x 15 13)
      have b51589 := hb (x 16 12)
      clear * - r51583 e51584 e51585 b51586 b51587 b51588 b51589 d51528
      omega
    have d51590 : (x 16 1 && x 16 12).toNat = 0 := by
      have r51591 := hand2 (x 16 1) (x 16 12)
      have b51592 := hb (x 16 12)
      have b51593 := hb (x 16 1 && x 16 12)
      clear * - r51591 b51592 b51593 d51582
      omega
    have d51594 : (x 14 2).toNat = 0 := by
      have r51595 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
      have e51596 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
      have e51597 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
      have b51598 := hb (x 13 3)
      have b51599 := hb (x 14 2)
      have b51600 := hb (x 15 13)
      have b51601 := hb (x 16 12)
      clear * - r51595 e51596 e51597 b51598 b51599 b51600 b51601 d51582 d51528
      omega
    have d51602 : (x 16 13).toNat = 1 := by
      have r51603 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
      have b51604 := hb (x 14 2)
      have b51605 := hb (x 16 13)
      have b51606 := hb (x 15 1 && x 15 14)
      clear * - r51603 b51604 b51605 b51606 d51463 d51594
      omega
    have d51607 : (x 16 1).toNat = 1 := by
      have r51608 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
      have b51609 := hb (x 16 1)
      have b51610 := hb (x 16 13)
      clear * - r51608 b51609 b51610 d51602
      omega
    have d51611 : (x 17 14).toNat = 0 := by
      have r51612 : (x 17 14).toNat + (x 16 1).toNat = 1 := hd14 17
      have b51613 := hb (x 16 1)
      have b51614 := hb (x 17 14)
      clear * - r51612 b51613 b51614 d51607
      omega
    have d51615 : (x 17 1 && x 17 14).toNat = 0 := by
      have r51616 := hand2 (x 17 1) (x 17 14)
      have b51617 := hb (x 17 14)
      have b51618 := hb (x 17 1 && x 17 14)
      clear * - r51616 b51617 b51618 d51611
      omega
    have d51619 : (x 18 13).toNat = 1 := by
      have r51620 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := hcov13 18
      have b51621 := hb (x 16 2)
      have b51622 := hb (x 18 13)
      have b51623 := hb (x 17 1 && x 17 14)
      clear * - r51620 b51621 b51622 b51623 d51615 d51574
      omega
    have d51624 : (x 19 12).toNat = 0 := by
      have r51625 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
      have e51626 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e51627 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b51628 := hb (x 16 3)
      have b51629 := hb (x 17 2)
      have b51630 := hb (x 18 13)
      have b51631 := hb (x 19 12)
      clear * - r51625 e51626 e51627 b51628 b51629 b51630 b51631 d51619
      omega
    have d51632 : (x 17 2).toNat = 0 := by
      have r51633 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := hd12 19
      have e51634 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e51635 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have b51636 := hb (x 16 3)
      have b51637 := hb (x 17 2)
      have b51638 := hb (x 18 13)
      have b51639 := hb (x 19 12)
      clear * - r51633 e51634 e51635 b51636 b51637 b51638 b51639 d51624 d51619
      omega
    have d51640 : (x 19 13).toNat = 1 := by
      have r51641 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
      have b51642 := hb (x 17 2)
      have b51643 := hb (x 19 13)
      have b51644 := hb (x 18 1 && x 18 14)
      clear * - r51641 b51642 b51643 b51644 d51558 d51632
      omega
    have d51645 : (x 20 12).toNat = 0 := by
      have r51646 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
      have e51647 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e51648 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b51649 := hb (x 17 3)
      have b51650 := hb (x 18 2)
      have b51651 := hb (x 19 13)
      have b51652 := hb (x 20 12)
      clear * - r51646 e51647 e51648 b51649 b51650 b51651 b51652 d51640 d51562
      omega
    have d51653 : (x 17 3).toNat = 0 := by
      have r51654 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
      have e51655 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
      have e51656 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
      have b51657 := hb (x 17 3)
      have b51658 := hb (x 18 2)
      have b51659 := hb (x 19 13)
      have b51660 := hb (x 20 12)
      clear * - r51654 e51655 e51656 b51657 b51658 b51659 b51660 d51645 d51640 d51562
      omega
    have d51661 : (x 17 11).toNat = 0 := by
      have r51662 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
      have b51663 := hb (x 17 3)
      have b51664 := hb (x 17 11)
      clear * - r51662 b51663 b51664 d51653
      omega
    have d51665 : (x 17 12).toNat = 0 := by
      have r51666 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
      have e51667 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e51668 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b51669 := hb (x 14 3)
      have b51670 := hb (x 15 2)
      have b51671 := hb (x 16 13)
      have b51672 := hb (x 17 12)
      clear * - r51666 e51667 e51668 b51669 b51670 b51671 b51672 d51602 d51467
      omega
    have d51673 : (x 14 3).toNat = 0 := by
      have r51674 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := hd12 17
      have e51675 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e51676 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b51677 := hb (x 14 3)
      have b51678 := hb (x 15 2)
      have b51679 := hb (x 16 13)
      have b51680 := hb (x 17 12)
      clear * - r51674 e51675 e51676 b51677 b51678 b51679 b51680 d51665 d51602 d51467
      omega
    have d51681 : (x 14 3 && x 14 14).toNat = 0 := by
      have r51682 := hand1 (x 14 3) (x 14 14)
      have b51683 := hb (x 14 3)
      have b51684 := hb (x 14 3 && x 14 14)
      clear * - r51682 b51683 b51684 d51673
      omega
    have r51685 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
    have b51686 := hb (x 13 4)
    have b51687 := hb (x 17 11)
    have b51688 := hb (x 16 1 && x 16 12)
    have b51689 := hb (x 15 2 && x 15 13)
    have b51690 := hb (x 14 3 && x 14 14)
    linarith only [r51685, b51686, b51687, b51688, b51689, b51690, d51661, d51590, d51471, d51681, d51499]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a1 (x : ℤ → Fin 16 → Bool)
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
    (g1 : (x 0 4).toNat = 1)
    (g2 : (x 0 10).toNat = 0)
    (g3 : (x 0 11).toNat = 0)
    (g4 : (x 1 2).toNat = 0)
    (g5 : (x 1 6).toNat = 0)
    (g6 : (x 1 10).toNat = 0)
    (g7 : (x 3 2).toNat = 0)
    (g8 : (x 3 4).toNat = 0)
    (g9 : (x 3 10).toNat = 0)
    (g10 : (x 1 2 && x 1 11).toNat = 0)
    (g11 : (x 0 3 && x 0 12).toNat = 0)
    (g12 : (x 0 1 && x 0 11).toNat = 0)
    (g13 : (x 1 2 && x 1 12).toNat = 0)
    (g14 : (x 0 3 && x 0 13).toNat = 0)
    (g15 : (x 3 2 && x 3 12).toNat = 0)
    (g16 : (x 1 4 && x 1 14).toNat = 0)
    (g17 : (x 1 2 && x 1 13).toNat = 0)
    (g18 : (x 0 3 && x 0 14).toNat = 0)
    (g19 : (x 0 1 && x 0 14).toNat = 0)
    (g20 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a1_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20
