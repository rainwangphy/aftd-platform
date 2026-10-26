import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000011001

Topic: combinatorics   Node: e3977d95ce4d

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiment 5738: on the integer window [-32, 32] the layer-free system refutes x(0,1) != x(0,14) as an integer program, not as an LP.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core: under the layer-free tight-cover constraints for k = 15 and 4 fixed bits of the class-type sequence near position 0 (a branch of the case split), the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000011001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 1 1).toNat = 1)
    (g1 : (x 1 2).toNat = 0)
    (g2 : (x 3 2).toNat = 0)
    (g3 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d40111 : (x 2 14).toNat = 0 := by
    have r40112 : (x 2 14).toNat + (x 1 1).toNat = 1 := hd14 2
    have b40113 := hb (x 1 1)
    have b40114 := hb (x 2 14)
    clear * - r40112 b40113 b40114 g0
    omega
  have d40115 : (x 2 1 && x 2 14).toNat = 0 := by
    have r40116 := hand2 (x 2 1) (x 2 14)
    have b40117 := hb (x 2 14)
    have b40118 := hb (x 2 1 && x 2 14)
    clear * - r40116 b40117 b40118 d40111
    omega
  have d40119 : (x 2 2).toNat = 0 := by
    have r40120 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
    have b40121 := hb (x 2 2)
    have b40122 := hb (x 2 14)
    clear * - r40120 b40121 b40122 d40111
    omega
  have d40123 : (x 4 13).toNat = 1 := by
    have r40124 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := hcov13 4
    have b40125 := hb (x 2 2)
    have b40126 := hb (x 4 13)
    have b40127 := hb (x 3 1 && x 3 14)
    clear * - r40124 b40125 b40126 b40127 g3 d40119
    omega
  have d40128 : (x 4 1).toNat = 1 := by
    have r40129 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
    have b40130 := hb (x 4 1)
    have b40131 := hb (x 4 13)
    clear * - r40129 b40130 b40131 d40123
    omega
  have d40132 : (x 5 14).toNat = 0 := by
    have r40133 : (x 5 14).toNat + (x 4 1).toNat = 1 := hd14 5
    have b40134 := hb (x 4 1)
    have b40135 := hb (x 5 14)
    clear * - r40133 b40134 b40135 d40128
    omega
  have d40136 : (x 5 1 && x 5 14).toNat = 0 := by
    have r40137 := hand2 (x 5 1) (x 5 14)
    have b40138 := hb (x 5 14)
    have b40139 := hb (x 5 1 && x 5 14)
    clear * - r40137 b40138 b40139 d40132
    omega
  have d40140 : (x 5 2).toNat = 0 := by
    have r40141 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
    have b40142 := hb (x 5 2)
    have b40143 := hb (x 5 14)
    clear * - r40141 b40142 b40143 d40132
    omega
  have d40144 : (x 3 13).toNat = 1 := by
    have r40145 : 1 ≤ (x 3 13).toNat + (x 2 1 && x 2 14).toNat + (x 1 2).toNat := hcov13 3
    have b40146 := hb (x 1 2)
    have b40147 := hb (x 3 13)
    have b40148 := hb (x 2 1 && x 2 14)
    clear * - r40145 b40146 b40147 b40148 d40115 g1
    omega
  have d40149 : (x 3 1).toNat = 1 := by
    have r40150 : (x 3 13).toNat ≤ (x 3 1).toNat := himp _ _ (hp13 3)
    have b40151 := hb (x 3 1)
    have b40152 := hb (x 3 13)
    clear * - r40150 b40151 b40152 d40144
    omega
  have d40153 : (x 4 14).toNat = 0 := by
    have r40154 : (x 4 14).toNat + (x 3 1).toNat = 1 := hd14 4
    have b40155 := hb (x 3 1)
    have b40156 := hb (x 4 14)
    clear * - r40154 b40155 b40156 d40149
    omega
  have d40157 : (x 4 1 && x 4 14).toNat = 0 := by
    have r40158 := hand2 (x 4 1) (x 4 14)
    have b40159 := hb (x 4 14)
    have b40160 := hb (x 4 1 && x 4 14)
    clear * - r40158 b40159 b40160 d40153
    omega
  have d40161 : (x 5 13).toNat = 1 := by
    have r40162 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := hcov13 5
    have b40163 := hb (x 3 2)
    have b40164 := hb (x 5 13)
    have b40165 := hb (x 4 1 && x 4 14)
    clear * - r40162 b40163 b40164 b40165 d40157 g2
    omega
  have d40166 : (x 5 1).toNat = 1 := by
    have r40167 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
    have b40168 := hb (x 5 1)
    have b40169 := hb (x 5 13)
    clear * - r40167 b40168 b40169 d40161
    omega
  have d40170 : (x 6 14).toNat = 0 := by
    have r40171 : (x 6 14).toNat + (x 5 1).toNat = 1 := hd14 6
    have b40172 := hb (x 5 1)
    have b40173 := hb (x 6 14)
    clear * - r40171 b40172 b40173 d40166
    omega
  have d40174 : (x 6 1 && x 6 14).toNat = 0 := by
    have r40175 := hand2 (x 6 1) (x 6 14)
    have b40176 := hb (x 6 14)
    have b40177 := hb (x 6 1 && x 6 14)
    clear * - r40175 b40176 b40177 d40170
    omega
  have d40178 : (x 7 13).toNat = 1 := by
    have r40179 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := hcov13 7
    have b40180 := hb (x 5 2)
    have b40181 := hb (x 7 13)
    have b40182 := hb (x 6 1 && x 6 14)
    clear * - r40179 b40180 b40181 b40182 d40174 d40140
    omega
  have d40183 : (x 7 1).toNat = 1 := by
    have r40184 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
    have b40185 := hb (x 7 1)
    have b40186 := hb (x 7 13)
    clear * - r40184 b40185 b40186 d40178
    omega
  have d40187 : (x 8 14).toNat = 0 := by
    have r40188 : (x 8 14).toNat + (x 7 1).toNat = 1 := hd14 8
    have b40189 := hb (x 7 1)
    have b40190 := hb (x 8 14)
    clear * - r40188 b40189 b40190 d40183
    omega
  have d40191 : (x 8 1 && x 8 14).toNat = 0 := by
    have r40192 := hand2 (x 8 1) (x 8 14)
    have b40193 := hb (x 8 14)
    have b40194 := hb (x 8 1 && x 8 14)
    clear * - r40192 b40193 b40194 d40187
    omega
  have d40195 : (x 8 2).toNat = 0 := by
    have r40196 : (x 8 2).toNat ≤ (x 8 14).toNat := himp _ _ (hp2 8)
    have b40197 := hb (x 8 2)
    have b40198 := hb (x 8 14)
    clear * - r40196 b40197 b40198 d40187
    omega
  have d40199 : (x 6 2).toNat = 0 := by
    have r40200 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
    have b40201 := hb (x 6 2)
    have b40202 := hb (x 6 14)
    clear * - r40200 b40201 b40202 d40170
    omega
  have d40203 : (x 4 2).toNat = 0 := by
    have r40204 : (x 4 2).toNat ≤ (x 4 14).toNat := himp _ _ (hp2 4)
    have b40205 := hb (x 4 2)
    have b40206 := hb (x 4 14)
    clear * - r40204 b40205 b40206 d40153
    omega
  have d40207 : (x 6 13).toNat = 1 := by
    have r40208 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := hcov13 6
    have b40209 := hb (x 4 2)
    have b40210 := hb (x 6 13)
    have b40211 := hb (x 5 1 && x 5 14)
    clear * - r40208 b40209 b40210 b40211 d40136 d40203
    omega
  have d40212 : (x 6 1).toNat = 1 := by
    have r40213 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
    have b40214 := hb (x 6 1)
    have b40215 := hb (x 6 13)
    clear * - r40213 b40214 b40215 d40207
    omega
  have d40216 : (x 7 14).toNat = 0 := by
    have r40217 : (x 7 14).toNat + (x 6 1).toNat = 1 := hd14 7
    have b40218 := hb (x 6 1)
    have b40219 := hb (x 7 14)
    clear * - r40217 b40218 b40219 d40212
    omega
  have d40220 : (x 7 1 && x 7 14).toNat = 0 := by
    have r40221 := hand2 (x 7 1) (x 7 14)
    have b40222 := hb (x 7 14)
    have b40223 := hb (x 7 1 && x 7 14)
    clear * - r40221 b40222 b40223 d40216
    omega
  have d40224 : (x 8 13).toNat = 1 := by
    have r40225 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := hcov13 8
    have b40226 := hb (x 6 2)
    have b40227 := hb (x 8 13)
    have b40228 := hb (x 7 1 && x 7 14)
    clear * - r40225 b40226 b40227 b40228 d40220 d40199
    omega
  have d40229 : (x 8 1).toNat = 1 := by
    have r40230 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
    have b40231 := hb (x 8 1)
    have b40232 := hb (x 8 13)
    clear * - r40230 b40231 b40232 d40224
    omega
  have d40233 : (x 9 14).toNat = 0 := by
    have r40234 : (x 9 14).toNat + (x 8 1).toNat = 1 := hd14 9
    have b40235 := hb (x 8 1)
    have b40236 := hb (x 9 14)
    clear * - r40234 b40235 b40236 d40229
    omega
  have d40237 : (x 9 1 && x 9 14).toNat = 0 := by
    have r40238 := hand2 (x 9 1) (x 9 14)
    have b40239 := hb (x 9 14)
    have b40240 := hb (x 9 1 && x 9 14)
    clear * - r40238 b40239 b40240 d40233
    omega
  have d40241 : (x 10 13).toNat = 1 := by
    have r40242 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := hcov13 10
    have b40243 := hb (x 8 2)
    have b40244 := hb (x 10 13)
    have b40245 := hb (x 9 1 && x 9 14)
    clear * - r40242 b40243 b40244 b40245 d40237 d40195
    omega
  have d40246 : (x 10 1).toNat = 1 := by
    have r40247 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
    have b40248 := hb (x 10 1)
    have b40249 := hb (x 10 13)
    clear * - r40247 b40248 b40249 d40241
    omega
  have d40250 : (x 11 14).toNat = 0 := by
    have r40251 : (x 11 14).toNat + (x 10 1).toNat = 1 := hd14 11
    have b40252 := hb (x 10 1)
    have b40253 := hb (x 11 14)
    clear * - r40251 b40252 b40253 d40246
    omega
  have d40254 : (x 11 1 && x 11 14).toNat = 0 := by
    have r40255 := hand2 (x 11 1) (x 11 14)
    have b40256 := hb (x 11 14)
    have b40257 := hb (x 11 1 && x 11 14)
    clear * - r40255 b40256 b40257 d40250
    omega
  have d40258 : (x 11 2).toNat = 0 := by
    have r40259 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
    have b40260 := hb (x 11 2)
    have b40261 := hb (x 11 14)
    clear * - r40259 b40260 b40261 d40250
    omega
  have d40262 : (x 9 2).toNat = 0 := by
    have r40263 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
    have b40264 := hb (x 9 2)
    have b40265 := hb (x 9 14)
    clear * - r40263 b40264 b40265 d40233
    omega
  have d40266 : (x 7 2).toNat = 0 := by
    have r40267 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
    have b40268 := hb (x 7 2)
    have b40269 := hb (x 7 14)
    clear * - r40267 b40268 b40269 d40216
    omega
  have d40270 : (x 9 13).toNat = 1 := by
    have r40271 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := hcov13 9
    have b40272 := hb (x 7 2)
    have b40273 := hb (x 9 13)
    have b40274 := hb (x 8 1 && x 8 14)
    clear * - r40271 b40272 b40273 b40274 d40191 d40266
    omega
  have d40275 : (x 9 1).toNat = 1 := by
    have r40276 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
    have b40277 := hb (x 9 1)
    have b40278 := hb (x 9 13)
    clear * - r40276 b40277 b40278 d40270
    omega
  have d40279 : (x 10 14).toNat = 0 := by
    have r40280 : (x 10 14).toNat + (x 9 1).toNat = 1 := hd14 10
    have b40281 := hb (x 9 1)
    have b40282 := hb (x 10 14)
    clear * - r40280 b40281 b40282 d40275
    omega
  have d40283 : (x 10 1 && x 10 14).toNat = 0 := by
    have r40284 := hand2 (x 10 1) (x 10 14)
    have b40285 := hb (x 10 14)
    have b40286 := hb (x 10 1 && x 10 14)
    clear * - r40284 b40285 b40286 d40279
    omega
  have d40287 : (x 11 13).toNat = 1 := by
    have r40288 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := hcov13 11
    have b40289 := hb (x 9 2)
    have b40290 := hb (x 11 13)
    have b40291 := hb (x 10 1 && x 10 14)
    clear * - r40288 b40289 b40290 b40291 d40283 d40262
    omega
  have d40292 : (x 11 1).toNat = 1 := by
    have r40293 : (x 11 13).toNat ≤ (x 11 1).toNat := himp _ _ (hp13 11)
    have b40294 := hb (x 11 1)
    have b40295 := hb (x 11 13)
    clear * - r40293 b40294 b40295 d40287
    omega
  have d40296 : (x 12 14).toNat = 0 := by
    have r40297 : (x 12 14).toNat + (x 11 1).toNat = 1 := hd14 12
    have b40298 := hb (x 11 1)
    have b40299 := hb (x 12 14)
    clear * - r40297 b40298 b40299 d40292
    omega
  have d40300 : (x 12 1 && x 12 14).toNat = 0 := by
    have r40301 := hand2 (x 12 1) (x 12 14)
    have b40302 := hb (x 12 14)
    have b40303 := hb (x 12 1 && x 12 14)
    clear * - r40301 b40302 b40303 d40296
    omega
  have d40304 : (x 13 13).toNat = 1 := by
    have r40305 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := hcov13 13
    have b40306 := hb (x 11 2)
    have b40307 := hb (x 13 13)
    have b40308 := hb (x 12 1 && x 12 14)
    clear * - r40305 b40306 b40307 b40308 d40300 d40258
    omega
  have d40309 : (x 13 1).toNat = 1 := by
    have r40310 : (x 13 13).toNat ≤ (x 13 1).toNat := himp _ _ (hp13 13)
    have b40311 := hb (x 13 1)
    have b40312 := hb (x 13 13)
    clear * - r40310 b40311 b40312 d40304
    omega
  have d40313 : (x 14 14).toNat = 0 := by
    have r40314 : (x 14 14).toNat + (x 13 1).toNat = 1 := hd14 14
    have b40315 := hb (x 13 1)
    have b40316 := hb (x 14 14)
    clear * - r40314 b40315 b40316 d40309
    omega
  have d40317 : (x 14 1 && x 14 14).toNat = 0 := by
    have r40318 := hand2 (x 14 1) (x 14 14)
    have b40319 := hb (x 14 14)
    have b40320 := hb (x 14 1 && x 14 14)
    clear * - r40318 b40319 b40320 d40313
    omega
  have d40321 : (x 14 3 && x 14 14).toNat = 0 := by
    have r40322 := hand2 (x 14 3) (x 14 14)
    have b40323 := hb (x 14 14)
    have b40324 := hb (x 14 3 && x 14 14)
    clear * - r40322 b40323 b40324 d40313
    omega
  have d40325 : (x 14 2).toNat = 0 := by
    have r40326 : (x 14 2).toNat ≤ (x 14 14).toNat := himp _ _ (hp2 14)
    have b40327 := hb (x 14 2)
    have b40328 := hb (x 14 14)
    clear * - r40326 b40327 b40328 d40313
    omega
  have d40329 : (x 12 2).toNat = 0 := by
    have r40330 : (x 12 2).toNat ≤ (x 12 14).toNat := himp _ _ (hp2 12)
    have b40331 := hb (x 12 2)
    have b40332 := hb (x 12 14)
    clear * - r40330 b40331 b40332 d40296
    omega
  have d40333 : (x 10 2).toNat = 0 := by
    have r40334 : (x 10 2).toNat ≤ (x 10 14).toNat := himp _ _ (hp2 10)
    have b40335 := hb (x 10 2)
    have b40336 := hb (x 10 14)
    clear * - r40334 b40335 b40336 d40279
    omega
  have d40337 : (x 12 13).toNat = 1 := by
    have r40338 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := hcov13 12
    have b40339 := hb (x 10 2)
    have b40340 := hb (x 12 13)
    have b40341 := hb (x 11 1 && x 11 14)
    clear * - r40338 b40339 b40340 b40341 d40254 d40333
    omega
  have d40342 : (x 12 1).toNat = 1 := by
    have r40343 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
    have b40344 := hb (x 12 1)
    have b40345 := hb (x 12 13)
    clear * - r40343 b40344 b40345 d40337
    omega
  have d40346 : (x 13 14).toNat = 0 := by
    have r40347 : (x 13 14).toNat + (x 12 1).toNat = 1 := hd14 13
    have b40348 := hb (x 12 1)
    have b40349 := hb (x 13 14)
    clear * - r40347 b40348 b40349 d40342
    omega
  have d40350 : (x 13 1 && x 13 14).toNat = 0 := by
    have r40351 := hand2 (x 13 1) (x 13 14)
    have b40352 := hb (x 13 14)
    have b40353 := hb (x 13 1 && x 13 14)
    clear * - r40351 b40352 b40353 d40346
    omega
  have d40354 : (x 14 13).toNat = 1 := by
    have r40355 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := hcov13 14
    have b40356 := hb (x 12 2)
    have b40357 := hb (x 14 13)
    have b40358 := hb (x 13 1 && x 13 14)
    clear * - r40355 b40356 b40357 b40358 d40350 d40329
    omega
  have d40359 : (x 14 1).toNat = 1 := by
    have r40360 : (x 14 13).toNat ≤ (x 14 1).toNat := himp _ _ (hp13 14)
    have b40361 := hb (x 14 1)
    have b40362 := hb (x 14 13)
    clear * - r40360 b40361 b40362 d40354
    omega
  have d40363 : (x 15 14).toNat = 0 := by
    have r40364 : (x 15 14).toNat + (x 14 1).toNat = 1 := hd14 15
    have b40365 := hb (x 14 1)
    have b40366 := hb (x 15 14)
    clear * - r40364 b40365 b40366 d40359
    omega
  have d40367 : (x 15 1 && x 15 14).toNat = 0 := by
    have r40368 := hand2 (x 15 1) (x 15 14)
    have b40369 := hb (x 15 14)
    have b40370 := hb (x 15 1 && x 15 14)
    clear * - r40368 b40369 b40370 d40363
    omega
  have d40371 : (x 16 13).toNat = 1 := by
    have r40372 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := hcov13 16
    have b40373 := hb (x 14 2)
    have b40374 := hb (x 16 13)
    have b40375 := hb (x 15 1 && x 15 14)
    clear * - r40372 b40373 b40374 b40375 d40367 d40325
    omega
  have d40376 : (x 16 1).toNat = 1 := by
    have r40377 : (x 16 13).toNat ≤ (x 16 1).toNat := himp _ _ (hp13 16)
    have b40378 := hb (x 16 1)
    have b40379 := hb (x 16 13)
    clear * - r40377 b40378 b40379 d40371
    omega
  have d40380 : (x 17 14).toNat = 0 := by
    have r40381 : (x 17 14).toNat + (x 16 1).toNat = 1 := hd14 17
    have b40382 := hb (x 16 1)
    have b40383 := hb (x 17 14)
    clear * - r40381 b40382 b40383 d40376
    omega
  have d40384 : (x 17 2).toNat = 0 := by
    have r40385 : (x 17 2).toNat ≤ (x 17 14).toNat := himp _ _ (hp2 17)
    have b40386 := hb (x 17 2)
    have b40387 := hb (x 17 14)
    clear * - r40385 b40386 b40387 d40380
    omega
  have d40388 : (x 15 2).toNat = 0 := by
    have r40389 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
    have b40390 := hb (x 15 2)
    have b40391 := hb (x 15 14)
    clear * - r40389 b40390 b40391 d40363
    omega
  have d40392 : (x 15 2 && x 15 13).toNat = 0 := by
    have r40393 := hand1 (x 15 2) (x 15 13)
    have b40394 := hb (x 15 2)
    have b40395 := hb (x 15 2 && x 15 13)
    clear * - r40393 b40394 b40395 d40388
    omega
  have d40396 : (x 13 2).toNat = 0 := by
    have r40397 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
    have b40398 := hb (x 13 2)
    have b40399 := hb (x 13 14)
    clear * - r40397 b40398 b40399 d40346
    omega
  have d40400 : (x 15 13).toNat = 1 := by
    have r40401 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := hcov13 15
    have b40402 := hb (x 13 2)
    have b40403 := hb (x 15 13)
    have b40404 := hb (x 14 1 && x 14 14)
    clear * - r40401 b40402 b40403 b40404 d40317 d40396
    omega
  have d40405 : (x 15 1).toNat = 1 := by
    have r40406 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
    have b40407 := hb (x 15 1)
    have b40408 := hb (x 15 13)
    clear * - r40406 b40407 b40408 d40400
    omega
  have d40409 : (x 16 14).toNat = 0 := by
    have r40410 : (x 16 14).toNat + (x 15 1).toNat = 1 := hd14 16
    have b40411 := hb (x 15 1)
    have b40412 := hb (x 16 14)
    clear * - r40410 b40411 b40412 d40405
    omega
  have d40413 : (x 16 1 && x 16 14).toNat = 0 := by
    have r40414 := hand2 (x 16 1) (x 16 14)
    have b40415 := hb (x 16 14)
    have b40416 := hb (x 16 1 && x 16 14)
    clear * - r40414 b40415 b40416 d40409
    omega
  have d40417 : (x 17 13).toNat = 1 := by
    have r40418 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := hcov13 17
    have b40419 := hb (x 15 2)
    have b40420 := hb (x 17 13)
    have b40421 := hb (x 16 1 && x 16 14)
    clear * - r40418 b40419 b40420 b40421 d40413 d40388
    omega
  have d40422 : (x 17 1).toNat = 1 := by
    have r40423 : (x 17 13).toNat ≤ (x 17 1).toNat := himp _ _ (hp13 17)
    have b40424 := hb (x 17 1)
    have b40425 := hb (x 17 13)
    clear * - r40423 b40424 b40425 d40417
    omega
  have d40426 : (x 18 14).toNat = 0 := by
    have r40427 : (x 18 14).toNat + (x 17 1).toNat = 1 := hd14 18
    have b40428 := hb (x 17 1)
    have b40429 := hb (x 18 14)
    clear * - r40427 b40428 b40429 d40422
    omega
  have d40430 : (x 18 1 && x 18 14).toNat = 0 := by
    have r40431 := hand2 (x 18 1) (x 18 14)
    have b40432 := hb (x 18 14)
    have b40433 := hb (x 18 1 && x 18 14)
    clear * - r40431 b40432 b40433 d40426
    omega
  have d40434 : (x 19 13).toNat = 1 := by
    have r40435 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := hcov13 19
    have b40436 := hb (x 17 2)
    have b40437 := hb (x 19 13)
    have b40438 := hb (x 18 1 && x 18 14)
    clear * - r40435 b40436 b40437 b40438 d40430 d40384
    omega
  have d40439 : (x 18 2).toNat = 0 := by
    have r40440 : (x 18 2).toNat ≤ (x 18 14).toNat := himp _ _ (hp2 18)
    have b40441 := hb (x 18 2)
    have b40442 := hb (x 18 14)
    clear * - r40440 b40441 b40442 d40426
    omega
  have d40443 : (x 20 12).toNat = 0 := by
    have r40444 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
    have e40445 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e40446 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b40447 := hb (x 17 3)
    have b40448 := hb (x 18 2)
    have b40449 := hb (x 19 13)
    have b40450 := hb (x 20 12)
    clear * - r40444 e40445 e40446 b40447 b40448 b40449 b40450 d40434 d40439
    omega
  have d40451 : (x 17 3).toNat = 0 := by
    have r40452 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := hd12 20
    have e40453 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
    have e40454 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
    have b40455 := hb (x 17 3)
    have b40456 := hb (x 18 2)
    have b40457 := hb (x 19 13)
    have b40458 := hb (x 20 12)
    clear * - r40452 e40453 e40454 b40455 b40456 b40457 b40458 d40443 d40434 d40439
    omega
  have d40459 : (x 17 11).toNat = 0 := by
    have r40460 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
    have b40461 := hb (x 17 3)
    have b40462 := hb (x 17 11)
    clear * - r40460 b40461 b40462 d40451
    omega
  have d40463 : (x 16 12).toNat = 0 := by
    have r40464 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := hd12 16
    have e40465 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
    have e40466 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
    have b40467 := hb (x 13 3)
    have b40468 := hb (x 14 2)
    have b40469 := hb (x 15 13)
    have b40470 := hb (x 16 12)
    clear * - r40464 e40465 e40466 b40467 b40468 b40469 b40470 d40400 d40325
    omega
  have d40471 : (x 16 1 && x 16 12).toNat = 0 := by
    have r40472 := hand2 (x 16 1) (x 16 12)
    have b40473 := hb (x 16 12)
    have b40474 := hb (x 16 1 && x 16 12)
    clear * - r40472 b40473 b40474 d40463
    omega
  have d40475 : (x 13 12).toNat = 0 := by
    have r40476 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := hd12 13
    have e40477 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
    have e40478 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
    have b40479 := hb (x 10 3)
    have b40480 := hb (x 11 2)
    have b40481 := hb (x 12 13)
    have b40482 := hb (x 13 12)
    clear * - r40476 e40477 e40478 b40479 b40480 b40481 b40482 d40337 d40258
    omega
  have d40483 : (x 13 4).toNat = 0 := by
    have r40484 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
    have b40485 := hb (x 13 4)
    have b40486 := hb (x 13 12)
    clear * - r40484 b40485 b40486 d40475
    omega
  have r40487 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := hcov11 17
  have b40488 := hb (x 13 4)
  have b40489 := hb (x 17 11)
  have b40490 := hb (x 16 1 && x 16 12)
  have b40491 := hb (x 15 2 && x 15 13)
  have b40492 := hb (x 14 3 && x 14 14)
  linarith only [r40487, b40488, b40489, b40490, b40491, b40492, d40459, d40471, d40392, d40321, d40483]

theorem cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000011001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 1 1).toNat = 1)
    (g1 : (x 1 2).toNat = 0)
    (g2 : (x 3 2).toNat = 0)
    (g3 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_iff_fourteen_core_a000011001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3
