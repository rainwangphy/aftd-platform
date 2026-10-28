import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a11

Topic: combinatorics   Node: 2c877d56be2f

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core: under the layer-free tight-cover constraints for k = 15 and 23 fixed bits of the class-type sequence near position 0, the constraints are contradictory.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a11_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 6).toNat = 0)
    (g1 : (x (-4) 4).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 10).toNat = 0)
    (g4 : (x 0 6).toNat = 1)
    (g5 : (x 0 9).toNat = 0)
    (g6 : (x 2 5).toNat = 0)
    (g7 : (x 4 11).toNat = 0)
    (g8 : (x 5 10).toNat = 0)
    (g9 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g10 : (x 7 4 && x 7 8).toNat = 0)
    (g11 : (x 6 5 && x 6 9).toNat = 0)
    (g12 : (x 5 6 && x 5 10).toNat = 0)
    (g13 : (x 4 7 && x 4 11).toNat = 0)
    (g14 : (x 0 9 && x 0 14).toNat = 0)
    (g15 : (x 7 2 && x 7 8).toNat = 0)
    (g16 : (x 6 3 && x 6 9).toNat = 0)
    (g17 : (x 5 4 && x 5 10).toNat = 0)
    (g18 : (x 4 5 && x 4 11).toNat = 0)
    (g19 : (x (-4) 4 && x (-4) 13).toNat = 0)
    (g20 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g21 : (x 4 1 && x 4 11).toNat = 0)
    (g22 : (x 3 4 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d58144 : (x 0 14).toNat = 1 := by
    have r58145 : (x 0 6).toNat ≤ (x 0 14).toNat := himp _ _ (hp6 0)
    have b58146 := hb (x 0 6)
    have b58147 := hb (x 0 14)
    clear * - r58145 b58146 b58147 g4
    omega
  have d58148 : (x (-1) 1).toNat = 0 := by
    have r58149 : (x 0 14).toNat + (x (-1) 1).toNat = 1 := by have q := hd14 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b58150 := hb (x (-1) 1)
    have b58151 := hb (x 0 14)
    clear * - r58149 b58150 b58151 d58144
    omega
  have d58152 : (x (-1) 1 && x (-1) 14).toNat = 0 := by
    have r58153 := hand1 (x (-1) 1) (x (-1) 14)
    have b58154 := hb (x (-1) 1)
    have b58155 := hb (x (-1) 1 && x (-1) 14)
    clear * - r58153 b58154 b58155 d58148
    omega
  have d58156 : (x (-1) 1 && x (-1) 12).toNat = 0 := by
    have r58157 := hand1 (x (-1) 1) (x (-1) 12)
    have b58158 := hb (x (-1) 1)
    have b58159 := hb (x (-1) 1 && x (-1) 12)
    clear * - r58157 b58158 b58159 d58148
    omega
  have d58160 : (x (-1) 1 && x (-1) 10).toNat = 0 := by
    have r58161 := hand1 (x (-1) 1) (x (-1) 10)
    have b58162 := hb (x (-1) 1)
    have b58163 := hb (x (-1) 1 && x (-1) 10)
    clear * - r58161 b58162 b58163 d58148
    omega
  have d58164 : (x (-1) 13).toNat = 0 := by
    have r58165 : (x (-1) 13).toNat ≤ (x (-1) 1).toNat := himp _ _ (hp13 (-1))
    have b58166 := hb (x (-1) 1)
    have b58167 := hb (x (-1) 13)
    clear * - r58165 b58166 b58167 d58148
    omega
  have d58168 : (x (-1) 5).toNat = 0 := by
    have r58169 : (x (-1) 5).toNat ≤ (x (-1) 13).toNat := himp _ _ (hp5 (-1))
    have b58170 := hb (x (-1) 5)
    have b58171 := hb (x (-1) 13)
    clear * - r58169 b58170 b58171 d58164
    omega
  have d58172 : (x 6 8).toNat = 0 := by
    have r58173 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e58174 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e58175 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e58176 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e58177 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e58178 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e58179 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b58180 := hb (x (-1) 7)
    have b58181 := hb (x 0 6)
    have b58182 := hb (x 1 5)
    have b58183 := hb (x 2 4)
    have b58184 := hb (x 3 11)
    have b58185 := hb (x 4 10)
    have b58186 := hb (x 5 9)
    have b58187 := hb (x 6 8)
    clear * - r58173 e58174 e58175 e58176 e58177 e58178 e58179 b58180 b58181 b58182 b58183 b58184 b58185 b58186 b58187 g4
    omega
  have d58188 : (x 6 3 && x 6 8).toNat = 0 := by
    have r58189 := hand2 (x 6 3) (x 6 8)
    have b58190 := hb (x 6 8)
    have b58191 := hb (x 6 3 && x 6 8)
    clear * - r58189 b58190 b58191 d58172
    omega
  have d58192 : (x 5 9).toNat = 0 := by
    have r58193 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e58194 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e58195 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e58196 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e58197 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e58198 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e58199 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b58200 := hb (x (-1) 7)
    have b58201 := hb (x 0 6)
    have b58202 := hb (x 1 5)
    have b58203 := hb (x 2 4)
    have b58204 := hb (x 3 11)
    have b58205 := hb (x 4 10)
    have b58206 := hb (x 5 9)
    have b58207 := hb (x 6 8)
    clear * - r58193 e58194 e58195 e58196 e58197 e58198 e58199 b58200 b58201 b58202 b58203 b58204 b58205 b58206 b58207 d58172 g4
    omega
  have d58208 : (x 5 4 && x 5 9).toNat = 0 := by
    have r58209 := hand2 (x 5 4) (x 5 9)
    have b58210 := hb (x 5 9)
    have b58211 := hb (x 5 4 && x 5 9)
    clear * - r58209 b58210 b58211 d58192
    omega
  have d58212 : (x 4 10).toNat = 0 := by
    have r58213 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e58214 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e58215 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e58216 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e58217 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e58218 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e58219 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b58220 := hb (x (-1) 7)
    have b58221 := hb (x 0 6)
    have b58222 := hb (x 1 5)
    have b58223 := hb (x 2 4)
    have b58224 := hb (x 3 11)
    have b58225 := hb (x 4 10)
    have b58226 := hb (x 5 9)
    have b58227 := hb (x 6 8)
    clear * - r58213 e58214 e58215 e58216 e58217 e58218 e58219 b58220 b58221 b58222 b58223 b58224 b58225 b58226 b58227 d58172 d58192 g4
    omega
  have d58228 : (x 4 5 && x 4 10).toNat = 0 := by
    have r58229 := hand2 (x 4 5) (x 4 10)
    have b58230 := hb (x 4 10)
    have b58231 := hb (x 4 5 && x 4 10)
    clear * - r58229 b58230 b58231 d58212
    omega
  have d58232 : (x 3 11).toNat = 0 := by
    have r58233 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e58234 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e58235 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e58236 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e58237 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e58238 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e58239 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b58240 := hb (x (-1) 7)
    have b58241 := hb (x 0 6)
    have b58242 := hb (x 1 5)
    have b58243 := hb (x 2 4)
    have b58244 := hb (x 3 11)
    have b58245 := hb (x 4 10)
    have b58246 := hb (x 5 9)
    have b58247 := hb (x 6 8)
    clear * - r58233 e58234 e58235 e58236 e58237 e58238 e58239 b58240 b58241 b58242 b58243 b58244 b58245 b58246 b58247 d58172 d58192 d58212 g4
    omega
  have d58248 : (x 3 1 && x 3 11).toNat = 0 := by
    have r58249 := hand2 (x 3 1) (x 3 11)
    have b58250 := hb (x 3 11)
    have b58251 := hb (x 3 1 && x 3 11)
    clear * - r58249 b58250 b58251 d58232
    omega
  have d58252 : (x 3 6 && x 3 11).toNat = 0 := by
    have r58253 := hand2 (x 3 6) (x 3 11)
    have b58254 := hb (x 3 11)
    have b58255 := hb (x 3 6 && x 3 11)
    clear * - r58253 b58254 b58255 d58232
    omega
  have d58256 : (x 2 4).toNat = 0 := by
    have r58257 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e58258 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e58259 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e58260 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e58261 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e58262 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e58263 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b58264 := hb (x (-1) 7)
    have b58265 := hb (x 0 6)
    have b58266 := hb (x 1 5)
    have b58267 := hb (x 2 4)
    have b58268 := hb (x 3 11)
    have b58269 := hb (x 4 10)
    have b58270 := hb (x 5 9)
    have b58271 := hb (x 6 8)
    clear * - r58257 e58258 e58259 e58260 e58261 e58262 e58263 b58264 b58265 b58266 b58267 b58268 b58269 b58270 b58271 d58172 d58192 d58212 d58232 g4
    omega
  have d58272 : (x 2 4 && x 2 14).toNat = 0 := by
    have r58273 := hand1 (x 2 4) (x 2 14)
    have b58274 := hb (x 2 4)
    have b58275 := hb (x 2 4 && x 2 14)
    clear * - r58273 b58274 b58275 d58256
    omega
  have d58276 : (x 1 5).toNat = 0 := by
    have r58277 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e58278 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e58279 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e58280 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e58281 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e58282 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e58283 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have b58284 := hb (x (-1) 7)
    have b58285 := hb (x 0 6)
    have b58286 := hb (x 1 5)
    have b58287 := hb (x 2 4)
    have b58288 := hb (x 3 11)
    have b58289 := hb (x 4 10)
    have b58290 := hb (x 5 9)
    have b58291 := hb (x 6 8)
    clear * - r58277 e58278 e58279 e58280 e58281 e58282 e58283 b58284 b58285 b58286 b58287 b58288 b58289 b58290 b58291 d58172 d58192 d58212 d58232 d58256 g4
    omega
  cases h58292 : x 0 1
  · have f58293 : (x 0 1).toNat = 0 := by rw [h58292]; rfl
    have d58294 : (x 0 1 && x 0 14).toNat = 0 := by
      have r58295 := hand1 (x 0 1) (x 0 14)
      have b58296 := hb (x 0 1)
      have b58297 := hb (x 0 1 && x 0 14)
      clear * - r58295 b58296 b58297 f58293
      omega
    have d58298 : (x 0 13).toNat = 0 := by
      have r58299 : (x 0 13).toNat ≤ (x 0 1).toNat := himp _ _ (hp13 0)
      have b58300 := hb (x 0 1)
      have b58301 := hb (x 0 13)
      clear * - r58299 b58300 b58301 f58293
      omega
    have d58302 : (x 0 5).toNat = 0 := by
      have r58303 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
      have b58304 := hb (x 0 5)
      have b58305 := hb (x 0 13)
      clear * - r58303 b58304 b58305 d58298
      omega
    have d58306 : (x (-2) 2).toNat = 1 := by
      have r58307 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58308 := hb (x (-2) 2)
      have b58309 := hb (x 0 13)
      have b58310 := hb (x (-1) 1 && x (-1) 14)
      clear * - r58307 b58308 b58309 b58310 d58298 d58152
      omega
    have d58311 : (x 0 12).toNat = 0 := by
      have r58312 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e58313 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e58314 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b58315 := hb (x (-3) 3)
      have b58316 := hb (x (-2) 2)
      have b58317 := hb (x (-1) 13)
      have b58318 := hb (x 0 12)
      clear * - r58312 e58313 e58314 b58315 b58316 b58317 b58318 d58164 d58306
      omega
    have d58319 : (x 0 4).toNat = 0 := by
      have r58320 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
      have b58321 := hb (x 0 4)
      have b58322 := hb (x 0 12)
      clear * - r58320 b58321 b58322 d58311
      omega
    have d58323 : (x 0 4 && x 0 14).toNat = 0 := by
      have r58324 := hand1 (x 0 4) (x 0 14)
      have b58325 := hb (x 0 4)
      have b58326 := hb (x 0 4 && x 0 14)
      clear * - r58324 b58325 b58326 d58319
      omega
    have d58327 : (x (-3) 3).toNat = 0 := by
      have r58328 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e58329 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
      have e58330 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
      have b58331 := hb (x (-3) 3)
      have b58332 := hb (x (-2) 2)
      have b58333 := hb (x (-1) 13)
      have b58334 := hb (x 0 12)
      clear * - r58328 e58329 e58330 b58331 b58332 b58333 b58334 d58311 d58164 d58306
      omega
    have d58335 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
      have r58336 := hand1 (x (-3) 3) (x (-3) 14)
      have b58337 := hb (x (-3) 3)
      have b58338 := hb (x (-3) 3 && x (-3) 14)
      clear * - r58336 b58337 b58338 d58327
      omega
    have d58339 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
      have r58340 := hand1 (x (-3) 3) (x (-3) 12)
      have b58341 := hb (x (-3) 3)
      have b58342 := hb (x (-3) 3 && x (-3) 12)
      clear * - r58340 b58341 b58342 d58327
      omega
    have d58343 : (x (-2) 2 && x (-2) 11).toNat = 1 := by
      have r58344 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58345 := hb (x (-6) 6)
      have b58346 := hb (x 0 9)
      have b58347 := hb (x (-1) 1 && x (-1) 10)
      have b58348 := hb (x (-2) 2 && x (-2) 11)
      have b58349 := hb (x (-3) 3 && x (-3) 12)
      have b58350 := hb (x (-4) 4 && x (-4) 13)
      have b58351 := hb (x (-5) 5 && x (-5) 14)
      clear * - r58344 b58345 b58346 b58347 b58348 b58349 b58350 b58351 g5 d58160 d58339 g19 g20 g0
      omega
    have d58352 : (x (-2) 11).toNat = 1 := by
      have r58353 := hand2 (x (-2) 2) (x (-2) 11)
      have b58354 := hb (x (-2) 11)
      have b58355 := hb (x (-2) 2 && x (-2) 11)
      clear * - r58353 b58354 b58355 d58343
      omega
    have d58356 : (x (-2) 3).toNat = 1 := by
      have r58357 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
      have b58358 := hb (x (-2) 3)
      have b58359 := hb (x (-2) 11)
      clear * - r58357 b58358 b58359 d58352
      omega
    have d58360 : (x 1 12).toNat = 0 := by
      have r58361 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e58362 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e58363 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b58364 := hb (x (-2) 3)
      have b58365 := hb (x (-1) 2)
      have b58366 := hb (x 0 13)
      have b58367 := hb (x 1 12)
      clear * - r58361 e58362 e58363 b58364 b58365 b58366 b58367 d58298 d58356
      omega
    have d58368 : (x 1 4).toNat = 0 := by
      have r58369 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
      have b58370 := hb (x 1 4)
      have b58371 := hb (x 1 12)
      clear * - r58369 b58370 b58371 d58360
      omega
    have d58372 : (x 1 4 && x 1 14).toNat = 0 := by
      have r58373 := hand1 (x 1 4) (x 1 14)
      have b58374 := hb (x 1 4)
      have b58375 := hb (x 1 4 && x 1 14)
      clear * - r58373 b58374 b58375 d58368
      omega
    have d58376 : (x (-1) 2).toNat = 0 := by
      have r58377 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e58378 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
      have e58379 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
      have b58380 := hb (x (-2) 3)
      have b58381 := hb (x (-1) 2)
      have b58382 := hb (x 0 13)
      have b58383 := hb (x 1 12)
      clear * - r58377 e58378 e58379 b58380 b58381 b58382 b58383 d58360 d58298 d58356
      omega
    have d58384 : (x 1 13).toNat = 1 := by
      have r58385 : 1 ≤ (x 1 13).toNat + (x 0 1 && x 0 14).toNat + (x (-1) 2).toNat := by have q := hcov13 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58386 := hb (x (-1) 2)
      have b58387 := hb (x 1 13)
      have b58388 := hb (x 0 1 && x 0 14)
      clear * - r58385 b58386 b58387 b58388 d58294 d58376
      omega
    have d58389 : (x 1 1).toNat = 1 := by
      have r58390 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
      have b58391 := hb (x 1 1)
      have b58392 := hb (x 1 13)
      clear * - r58390 b58391 b58392 d58384
      omega
    have d58393 : (x 2 14).toNat = 0 := by
      have r58394 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58395 := hb (x 1 1)
      have b58396 := hb (x 2 14)
      clear * - r58394 b58395 b58396 d58389
      omega
    have d58397 : (x 2 3 && x 2 14).toNat = 0 := by
      have r58398 := hand2 (x 2 3) (x 2 14)
      have b58399 := hb (x 2 14)
      have b58400 := hb (x 2 3 && x 2 14)
      clear * - r58398 b58399 b58400 d58393
      omega
    have d58401 : (x 2 2).toNat = 0 := by
      have r58402 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
      have b58403 := hb (x 2 2)
      have b58404 := hb (x 2 14)
      clear * - r58402 b58403 b58404 d58393
      omega
    have d58405 : (x 2 2 && x 2 12).toNat = 0 := by
      have r58406 := hand1 (x 2 2) (x 2 12)
      have b58407 := hb (x 2 2)
      have b58408 := hb (x 2 2 && x 2 12)
      clear * - r58406 b58407 b58408 d58401
      omega
    have d58409 : (x 1 3 && x 1 13).toNat = 1 := by
      have r58410 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58411 := hb (x (-1) 5)
      have b58412 := hb (x 4 10)
      have b58413 := hb (x 3 1 && x 3 11)
      have b58414 := hb (x 2 2 && x 2 12)
      have b58415 := hb (x 1 3 && x 1 13)
      have b58416 := hb (x 0 4 && x 0 14)
      clear * - r58410 b58411 b58412 b58413 b58414 b58415 b58416 d58212 d58248 d58405 d58323 d58168
      omega
    have d58417 : (x 1 3).toNat = 1 := by
      have r58418 := hand1 (x 1 3) (x 1 13)
      have b58419 := hb (x 1 3)
      have b58420 := hb (x 1 3 && x 1 13)
      clear * - r58418 b58419 b58420 d58409
      omega
    have d58421 : (x 4 12).toNat = 0 := by
      have r58422 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e58423 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e58424 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b58425 := hb (x 1 3)
      have b58426 := hb (x 2 2)
      have b58427 := hb (x 3 13)
      have b58428 := hb (x 4 12)
      clear * - r58422 e58423 e58424 b58425 b58426 b58427 b58428 d58401 d58417
      omega
    have d58429 : (x 4 1 && x 4 12).toNat = 0 := by
      have r58430 := hand2 (x 4 1) (x 4 12)
      have b58431 := hb (x 4 12)
      have b58432 := hb (x 4 1 && x 4 12)
      clear * - r58430 b58431 b58432 d58421
      omega
    have d58433 : (x 4 2 && x 4 12).toNat = 0 := by
      have r58434 := hand2 (x 4 2) (x 4 12)
      have b58435 := hb (x 4 12)
      have b58436 := hb (x 4 2 && x 4 12)
      clear * - r58434 b58435 b58436 d58421
      omega
    have d58437 : (x 3 13).toNat = 0 := by
      have r58438 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e58439 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
      have e58440 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
      have b58441 := hb (x 1 3)
      have b58442 := hb (x 2 2)
      have b58443 := hb (x 3 13)
      have b58444 := hb (x 4 12)
      clear * - r58438 e58439 e58440 b58441 b58442 b58443 b58444 d58421 d58401 d58417
      omega
    have d58445 : (x 3 2 && x 3 13).toNat = 0 := by
      have r58446 := hand2 (x 3 2) (x 3 13)
      have b58447 := hb (x 3 13)
      have b58448 := hb (x 3 2 && x 3 13)
      clear * - r58446 b58447 b58448 d58437
      omega
    have d58449 : (x 5 11).toNat = 1 := by
      have r58450 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58451 := hb (x 1 4)
      have b58452 := hb (x 5 11)
      have b58453 := hb (x 4 1 && x 4 12)
      have b58454 := hb (x 3 2 && x 3 13)
      have b58455 := hb (x 2 3 && x 2 14)
      clear * - r58450 b58451 b58452 b58453 b58454 b58455 d58429 d58445 d58397 d58368
      omega
    have d58456 : (x 5 3).toNat = 1 := by
      have r58457 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
      have b58458 := hb (x 5 3)
      have b58459 := hb (x 5 11)
      clear * - r58457 b58458 b58459 d58449
      omega
    have d58460 : (x 8 12).toNat = 0 := by
      have r58461 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e58462 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e58463 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b58464 := hb (x 5 3)
      have b58465 := hb (x 6 2)
      have b58466 := hb (x 7 13)
      have b58467 := hb (x 8 12)
      clear * - r58461 e58462 e58463 b58464 b58465 b58466 b58467 d58456
      omega
    have d58468 : (x 7 13).toNat = 0 := by
      have r58469 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e58470 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e58471 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b58472 := hb (x 5 3)
      have b58473 := hb (x 6 2)
      have b58474 := hb (x 7 13)
      have b58475 := hb (x 8 12)
      clear * - r58469 e58470 e58471 b58472 b58473 b58474 b58475 d58460 d58456
      omega
    have d58476 : (x 6 2).toNat = 0 := by
      have r58477 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e58478 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
      have e58479 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
      have b58480 := hb (x 5 3)
      have b58481 := hb (x 6 2)
      have b58482 := hb (x 7 13)
      have b58483 := hb (x 8 12)
      clear * - r58477 e58478 e58479 b58480 b58481 b58482 b58483 d58460 d58468 d58456
      omega
    have d58484 : (x 6 10).toNat = 0 := by
      have r58485 : (x 6 10).toNat ≤ (x 6 2).toNat := himp _ _ (hp10 6)
      have b58486 := hb (x 6 2)
      have b58487 := hb (x 6 10)
      clear * - r58485 b58486 b58487 d58476
      omega
    have d58488 : (x 3 3 && x 3 13).toNat = 0 := by
      have r58489 := hand2 (x 3 3) (x 3 13)
      have b58490 := hb (x 3 13)
      have b58491 := hb (x 3 3 && x 3 13)
      clear * - r58489 b58490 b58491 d58437
      omega
    have d58492 : (x 5 1 && x 5 11).toNat = 1 := by
      have r58493 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58494 := hb (x 1 5)
      have b58495 := hb (x 6 10)
      have b58496 := hb (x 5 1 && x 5 11)
      have b58497 := hb (x 4 2 && x 4 12)
      have b58498 := hb (x 3 3 && x 3 13)
      have b58499 := hb (x 2 4 && x 2 14)
      clear * - r58493 b58494 b58495 b58496 b58497 b58498 b58499 d58484 d58433 d58488 d58272 d58276
      omega
    have d58500 : (x 5 1).toNat = 1 := by
      have r58501 := hand1 (x 5 1) (x 5 11)
      have b58502 := hb (x 5 1)
      have b58503 := hb (x 5 1 && x 5 11)
      clear * - r58501 b58502 b58503 d58492
      omega
    have d58504 : (x 6 14).toNat = 0 := by
      have r58505 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58506 := hb (x 5 1)
      have b58507 := hb (x 6 14)
      clear * - r58505 b58506 b58507 d58500
      omega
    have d58508 : (x 6 1 && x 6 14).toNat = 0 := by
      have r58509 := hand2 (x 6 1) (x 6 14)
      have b58510 := hb (x 6 14)
      have b58511 := hb (x 6 1 && x 6 14)
      clear * - r58509 b58510 b58511 d58504
      omega
    have d58512 : (x 5 2).toNat = 1 := by
      have r58513 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58514 := hb (x 5 2)
      have b58515 := hb (x 7 13)
      have b58516 := hb (x 6 1 && x 6 14)
      clear * - r58513 b58514 b58515 b58516 d58468 d58508
      omega
    have d58517 : (x 5 14).toNat = 1 := by
      have r58518 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
      have b58519 := hb (x 5 2)
      have b58520 := hb (x 5 14)
      clear * - r58518 b58519 b58520 d58512
      omega
    have d58521 : (x 4 1).toNat = 0 := by
      have r58522 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58523 := hb (x 4 1)
      have b58524 := hb (x 5 14)
      clear * - r58522 b58523 b58524 d58517
      omega
    have d58525 : (x 4 13).toNat = 0 := by
      have r58526 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
      have b58527 := hb (x 4 1)
      have b58528 := hb (x 4 13)
      clear * - r58526 b58527 b58528 d58521
      omega
    have d58529 : (x 3 1 && x 3 14).toNat = 1 := by
      have r58530 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58531 := hb (x 2 2)
      have b58532 := hb (x 4 13)
      have b58533 := hb (x 3 1 && x 3 14)
      clear * - r58530 b58531 b58532 b58533 d58525 d58401
      omega
    have d58534 : (x 3 14).toNat = 1 := by
      have r58535 := hand2 (x 3 1) (x 3 14)
      have b58536 := hb (x 3 14)
      have b58537 := hb (x 3 1 && x 3 14)
      clear * - r58535 b58536 b58537 d58529
      omega
    have d58538 : (x 2 1).toNat = 0 := by
      have r58539 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58540 := hb (x 2 1)
      have b58541 := hb (x 3 14)
      clear * - r58539 b58540 b58541 d58534
      omega
    have d58542 : (x 2 1 && x 2 12).toNat = 0 := by
      have r58543 := hand1 (x 2 1) (x 2 12)
      have b58544 := hb (x 2 1)
      have b58545 := hb (x 2 1 && x 2 12)
      clear * - r58543 b58544 b58545 d58538
      omega
    have d58546 : (x 2 13).toNat = 0 := by
      have r58547 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
      have b58548 := hb (x 2 1)
      have b58549 := hb (x 2 13)
      clear * - r58547 b58548 b58549 d58538
      omega
    have d58550 : (x 2 3 && x 2 13).toNat = 0 := by
      have r58551 := hand2 (x 2 3) (x 2 13)
      have b58552 := hb (x 2 13)
      have b58553 := hb (x 2 3 && x 2 13)
      clear * - r58551 b58552 b58553 d58546
      omega
    have d58554 : (x 3 2 && x 3 12).toNat = 1 := by
      have r58555 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58556 := hb (x 0 5)
      have b58557 := hb (x 5 10)
      have b58558 := hb (x 4 1 && x 4 11)
      have b58559 := hb (x 3 2 && x 3 12)
      have b58560 := hb (x 2 3 && x 2 13)
      have b58561 := hb (x 1 4 && x 1 14)
      clear * - r58555 b58556 b58557 b58558 b58559 b58560 b58561 g8 g21 d58550 d58372 d58302
      omega
    have d58562 : (x 3 12).toNat = 1 := by
      have r58563 := hand2 (x 3 2) (x 3 12)
      have b58564 := hb (x 3 12)
      have b58565 := hb (x 3 2 && x 3 12)
      clear * - r58563 b58564 b58565 d58554
      omega
    have d58566 : (x 1 2).toNat = 0 := by
      have r58567 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e58568 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e58569 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b58570 := hb (x 0 3)
      have b58571 := hb (x 1 2)
      have b58572 := hb (x 2 13)
      have b58573 := hb (x 3 12)
      clear * - r58567 e58568 e58569 b58570 b58571 b58572 b58573 d58562 d58546
      omega
    have d58574 : (x 1 2 && x 1 13).toNat = 0 := by
      have r58575 := hand1 (x 1 2) (x 1 13)
      have b58576 := hb (x 1 2)
      have b58577 := hb (x 1 2 && x 1 13)
      clear * - r58575 b58576 b58577 d58566
      omega
    have d58578 : (x 0 3).toNat = 0 := by
      have r58579 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e58580 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
      have e58581 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
      have b58582 := hb (x 0 3)
      have b58583 := hb (x 1 2)
      have b58584 := hb (x 2 13)
      have b58585 := hb (x 3 12)
      clear * - r58579 e58580 e58581 b58582 b58583 b58584 b58585 d58562 d58546 d58566
      omega
    have d58586 : (x 0 3 && x 0 14).toNat = 0 := by
      have r58587 := hand1 (x 0 3) (x 0 14)
      have b58588 := hb (x 0 3)
      have b58589 := hb (x 0 3 && x 0 14)
      clear * - r58587 b58588 b58589 d58578
      omega
    have d58590 : (x (-1) 4).toNat = 1 := by
      have r58591 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58592 := hb (x (-1) 4)
      have b58593 := hb (x 3 11)
      have b58594 := hb (x 2 1 && x 2 12)
      have b58595 := hb (x 1 2 && x 1 13)
      have b58596 := hb (x 0 3 && x 0 14)
      clear * - r58591 b58592 b58593 b58594 b58595 b58596 d58232 d58542 d58574 d58586
      omega
    have d58597 : (x (-1) 12).toNat = 1 := by
      have r58598 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
      have b58599 := hb (x (-1) 4)
      have b58600 := hb (x (-1) 12)
      clear * - r58598 b58599 b58600 d58590
      omega
    have d58601 : (x (-2) 13).toNat = 0 := by
      have r58602 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e58603 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
      have e58604 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
      have b58605 := hb (x (-4) 3)
      have b58606 := hb (x (-3) 2)
      have b58607 := hb (x (-2) 13)
      have b58608 := hb (x (-1) 12)
      clear * - r58602 e58603 e58604 b58605 b58606 b58607 b58608 d58597
      omega
    have d58609 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
      have r58610 := hand2 (x (-2) 2) (x (-2) 13)
      have b58611 := hb (x (-2) 13)
      have b58612 := hb (x (-2) 2 && x (-2) 13)
      clear * - r58610 b58611 b58612 d58601
      omega
    have d58613 : (x 0 11).toNat = 1 := by
      have r58614 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58615 := hb (x (-4) 4)
      have b58616 := hb (x 0 11)
      have b58617 := hb (x (-1) 1 && x (-1) 12)
      have b58618 := hb (x (-2) 2 && x (-2) 13)
      have b58619 := hb (x (-3) 3 && x (-3) 14)
      clear * - r58614 b58615 b58616 b58617 b58618 b58619 d58156 d58609 d58335 g1
      omega
    have r58620 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
    have b58621 := hb (x 0 3)
    have b58622 := hb (x 0 11)
    linarith only [r58620, b58621, b58622, d58613, d58578]
  · have f58623 : (x 0 1).toNat = 1 := by rw [h58292]; rfl
    have d58624 : (x 1 14).toNat = 0 := by
      have r58625 : (x 1 14).toNat + (x 0 1).toNat = 1 := by have q := hd14 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b58626 := hb (x 0 1)
      have b58627 := hb (x 1 14)
      clear * - r58625 b58626 b58627 f58623
      omega
    have d58628 : (x 1 1 && x 1 14).toNat = 0 := by
      have r58629 := hand2 (x 1 1) (x 1 14)
      have b58630 := hb (x 1 14)
      have b58631 := hb (x 1 1 && x 1 14)
      clear * - r58629 b58630 b58631 d58624
      omega
    have d58632 : (x 1 3 && x 1 14).toNat = 0 := by
      have r58633 := hand2 (x 1 3) (x 1 14)
      have b58634 := hb (x 1 14)
      have b58635 := hb (x 1 3 && x 1 14)
      clear * - r58633 b58634 b58635 d58624
      omega
    have d58636 : (x 1 4 && x 1 14).toNat = 0 := by
      have r58637 := hand2 (x 1 4) (x 1 14)
      have b58638 := hb (x 1 14)
      have b58639 := hb (x 1 4 && x 1 14)
      clear * - r58637 b58638 b58639 d58624
      omega
    have d58640 : (x 1 8 && x 1 14).toNat = 0 := by
      have r58641 := hand2 (x 1 8) (x 1 14)
      have b58642 := hb (x 1 14)
      have b58643 := hb (x 1 8 && x 1 14)
      clear * - r58641 b58642 b58643 d58624
      omega
    have d58644 : (x 1 2).toNat = 0 := by
      have r58645 : (x 1 2).toNat ≤ (x 1 14).toNat := himp _ _ (hp2 1)
      have b58646 := hb (x 1 2)
      have b58647 := hb (x 1 14)
      clear * - r58645 b58646 b58647 d58624
      omega
    have d58648 : (x 1 2 && x 1 12).toNat = 0 := by
      have r58649 := hand1 (x 1 2) (x 1 12)
      have b58650 := hb (x 1 2)
      have b58651 := hb (x 1 2 && x 1 12)
      clear * - r58649 b58650 b58651 d58644
      omega
    have d58652 : (x 1 10).toNat = 0 := by
      have r58653 : (x 1 10).toNat ≤ (x 1 2).toNat := himp _ _ (hp10 1)
      have b58654 := hb (x 1 2)
      have b58655 := hb (x 1 10)
      clear * - r58653 b58654 b58655 d58644
      omega
    cases h58656 : x 0 2
    · have f58657 : (x 0 2).toNat = 0 := by rw [h58656]; rfl
      have d58658 : (x 0 10).toNat = 0 := by
        have r58659 : (x 0 10).toNat ≤ (x 0 2).toNat := himp _ _ (hp10 0)
        have b58660 := hb (x 0 2)
        have b58661 := hb (x 0 10)
        clear * - r58659 b58660 b58661 f58657
        omega
      have d58662 : (x 0 1 && x 0 10).toNat = 0 := by
        have r58663 := hand2 (x 0 1) (x 0 10)
        have b58664 := hb (x 0 10)
        have b58665 := hb (x 0 1 && x 0 10)
        clear * - r58663 b58664 b58665 d58658
        omega
      have d58666 : (x 2 13).toNat = 1 := by
        have r58667 : 1 ≤ (x 2 13).toNat + (x 1 1 && x 1 14).toNat + (x 0 2).toNat := by have q := hcov13 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b58668 := hb (x 0 2)
        have b58669 := hb (x 2 13)
        have b58670 := hb (x 1 1 && x 1 14)
        clear * - r58667 b58668 b58669 b58670 d58628 f58657
        omega
      have d58671 : (x 2 1).toNat = 1 := by
        have r58672 : (x 2 13).toNat ≤ (x 2 1).toNat := himp _ _ (hp13 2)
        have b58673 := hb (x 2 1)
        have b58674 := hb (x 2 13)
        clear * - r58672 b58673 b58674 d58666
        omega
      have d58675 : (x 3 14).toNat = 0 := by
        have r58676 : (x 3 14).toNat + (x 2 1).toNat = 1 := by have q := hd14 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b58677 := hb (x 2 1)
        have b58678 := hb (x 3 14)
        clear * - r58676 b58677 b58678 d58671
        omega
      have d58679 : (x 3 3 && x 3 14).toNat = 0 := by
        have r58680 := hand2 (x 3 3) (x 3 14)
        have b58681 := hb (x 3 14)
        have b58682 := hb (x 3 3 && x 3 14)
        clear * - r58680 b58681 b58682 d58675
        omega
      have d58683 : (x 3 6).toNat = 0 := by
        have r58684 : (x 3 6).toNat ≤ (x 3 14).toNat := himp _ _ (hp6 3)
        have b58685 := hb (x 3 6)
        have b58686 := hb (x 3 14)
        clear * - r58684 b58685 b58686 d58675
        omega
      have d58687 : (x 3 6 && x 3 12).toNat = 0 := by
        have r58688 := hand1 (x 3 6) (x 3 12)
        have b58689 := hb (x 3 6)
        have b58690 := hb (x 3 6 && x 3 12)
        clear * - r58688 b58689 b58690 d58683
        omega
      have d58691 : (x 3 2).toNat = 0 := by
        have r58692 : (x 3 2).toNat ≤ (x 3 14).toNat := himp _ _ (hp2 3)
        have b58693 := hb (x 3 2)
        have b58694 := hb (x 3 14)
        clear * - r58692 b58693 b58694 d58675
        omega
      have d58695 : (x 3 2 && x 3 12).toNat = 0 := by
        have r58696 := hand1 (x 3 2) (x 3 12)
        have b58697 := hb (x 3 2)
        have b58698 := hb (x 3 2 && x 3 12)
        clear * - r58696 b58697 b58698 d58691
        omega
      have d58699 : (x 3 10).toNat = 0 := by
        have r58700 : (x 3 10).toNat ≤ (x 3 2).toNat := himp _ _ (hp10 3)
        have b58701 := hb (x 3 2)
        have b58702 := hb (x 3 10)
        clear * - r58700 b58701 b58702 d58691
        omega
      have d58703 : (x 3 12).toNat = 0 := by
        have r58704 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e58705 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e58706 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b58707 := hb (x 0 3)
        have b58708 := hb (x 1 2)
        have b58709 := hb (x 2 13)
        have b58710 := hb (x 3 12)
        clear * - r58704 e58705 e58706 b58707 b58708 b58709 b58710 d58666 d58644
        omega
      have d58711 : (x 3 1 && x 3 12).toNat = 0 := by
        have r58712 := hand2 (x 3 1) (x 3 12)
        have b58713 := hb (x 3 12)
        have b58714 := hb (x 3 1 && x 3 12)
        clear * - r58712 b58713 b58714 d58703
        omega
      have d58715 : (x 3 8 && x 3 12).toNat = 0 := by
        have r58716 := hand2 (x 3 8) (x 3 12)
        have b58717 := hb (x 3 12)
        have b58718 := hb (x 3 8 && x 3 12)
        clear * - r58716 b58717 b58718 d58703
        omega
      have d58719 : (x 0 3).toNat = 0 := by
        have r58720 : (x 3 12).toNat + (x 2 1 && x 2 13).toNat + (x 1 2 && x 1 14).toNat + (x 0 3).toNat = 1 := by have q := hd12 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e58721 : (x 2 1 && x 2 13).toNat = (x 2 13).toNat := handr _ _ (fun h => hp13 2 (h))
        have e58722 : (x 1 2 && x 1 14).toNat = (x 1 2).toNat := handl _ _ (fun h => hp2 1 (h))
        have b58723 := hb (x 0 3)
        have b58724 := hb (x 1 2)
        have b58725 := hb (x 2 13)
        have b58726 := hb (x 3 12)
        clear * - r58720 e58721 e58722 b58723 b58724 b58725 b58726 d58703 d58666 d58644
        omega
      have d58727 : (x 0 3 && x 0 13).toNat = 0 := by
        have r58728 := hand1 (x 0 3) (x 0 13)
        have b58729 := hb (x 0 3)
        have b58730 := hb (x 0 3 && x 0 13)
        clear * - r58728 b58729 b58730 d58719
        omega
      have d58731 : (x 0 11).toNat = 0 := by
        have r58732 : (x 0 11).toNat ≤ (x 0 3).toNat := himp _ _ (hp11 0)
        have b58733 := hb (x 0 3)
        have b58734 := hb (x 0 11)
        clear * - r58732 b58733 b58734 d58719
        omega
      have d58735 : (x 0 1 && x 0 11).toNat = 0 := by
        have r58736 := hand2 (x 0 1) (x 0 11)
        have b58737 := hb (x 0 11)
        have b58738 := hb (x 0 1 && x 0 11)
        clear * - r58736 b58737 b58738 d58731
        omega
      cases h58739 : x 0 4
      · have f58740 : (x 0 4).toNat = 0 := by rw [h58739]; rfl
        have d58741 : (x 0 4 && x 0 14).toNat = 0 := by
          have r58742 := hand1 (x 0 4) (x 0 14)
          have b58743 := hb (x 0 4)
          have b58744 := hb (x 0 4 && x 0 14)
          clear * - r58742 b58743 b58744 f58740
          omega
        have d58745 : (x 2 2 && x 2 13).toNat = 1 := by
          have r58746 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b58747 := hb (x 0 4)
          have b58748 := hb (x 4 11)
          have b58749 := hb (x 3 1 && x 3 12)
          have b58750 := hb (x 2 2 && x 2 13)
          have b58751 := hb (x 1 3 && x 1 14)
          clear * - r58746 b58747 b58748 b58749 b58750 b58751 g7 d58711 d58632 f58740
          omega
        have d58752 : (x 2 2).toNat = 1 := by
          have r58753 := hand1 (x 2 2) (x 2 13)
          have b58754 := hb (x 2 2)
          have b58755 := hb (x 2 2 && x 2 13)
          clear * - r58753 b58754 b58755 d58745
          omega
        have d58756 : (x 2 14).toNat = 1 := by
          have r58757 : (x 2 2).toNat ≤ (x 2 14).toNat := himp _ _ (hp2 2)
          have b58758 := hb (x 2 2)
          have b58759 := hb (x 2 14)
          clear * - r58757 b58758 b58759 d58752
          omega
        have d58760 : (x 1 1).toNat = 0 := by
          have r58761 : (x 2 14).toNat + (x 1 1).toNat = 1 := by have q := hd14 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b58762 := hb (x 1 1)
          have b58763 := hb (x 2 14)
          clear * - r58761 b58762 b58763 d58756
          omega
        have d58764 : (x 1 13).toNat = 0 := by
          have r58765 : (x 1 13).toNat ≤ (x 1 1).toNat := himp _ _ (hp13 1)
          have b58766 := hb (x 1 1)
          have b58767 := hb (x 1 13)
          clear * - r58765 b58766 b58767 d58760
          omega
        have d58768 : (x 1 3 && x 1 13).toNat = 0 := by
          have r58769 := hand2 (x 1 3) (x 1 13)
          have b58770 := hb (x 1 13)
          have b58771 := hb (x 1 3 && x 1 13)
          clear * - r58769 b58770 b58771 d58764
          omega
        have d58772 : (x 1 8 && x 1 13).toNat = 0 := by
          have r58773 := hand2 (x 1 8) (x 1 13)
          have b58774 := hb (x 1 13)
          have b58775 := hb (x 1 8 && x 1 13)
          clear * - r58773 b58774 b58775 d58764
          omega
        have d58776 : (x 1 9).toNat = 0 := by
          have r58777 : (x 1 9).toNat ≤ (x 1 1).toNat := himp _ _ (hp9 1)
          have b58778 := hb (x 1 1)
          have b58779 := hb (x 1 9)
          clear * - r58777 b58778 b58779 d58760
          omega
        have d58780 : (x 4 12).toNat = 0 := by
          have r58781 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e58782 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e58783 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b58784 := hb (x 1 3)
          have b58785 := hb (x 2 2)
          have b58786 := hb (x 3 13)
          have b58787 := hb (x 4 12)
          clear * - r58781 e58782 e58783 b58784 b58785 b58786 b58787 d58752
          omega
        have d58788 : (x 4 2 && x 4 12).toNat = 0 := by
          have r58789 := hand2 (x 4 2) (x 4 12)
          have b58790 := hb (x 4 12)
          have b58791 := hb (x 4 2 && x 4 12)
          clear * - r58789 b58790 b58791 d58780
          omega
        have d58792 : (x 4 4).toNat = 0 := by
          have r58793 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
          have b58794 := hb (x 4 4)
          have b58795 := hb (x 4 12)
          clear * - r58793 b58794 b58795 d58780
          omega
        have d58796 : (x 4 4 && x 4 8).toNat = 0 := by
          have r58797 := hand1 (x 4 4) (x 4 8)
          have b58798 := hb (x 4 4)
          have b58799 := hb (x 4 4 && x 4 8)
          clear * - r58797 b58798 b58799 d58792
          omega
        have d58800 : (x 3 13).toNat = 0 := by
          have r58801 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e58802 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e58803 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b58804 := hb (x 1 3)
          have b58805 := hb (x 2 2)
          have b58806 := hb (x 3 13)
          have b58807 := hb (x 4 12)
          clear * - r58801 e58802 e58803 b58804 b58805 b58806 b58807 d58780 d58752
          omega
        have d58808 : (x 3 3 && x 3 13).toNat = 0 := by
          have r58809 := hand2 (x 3 3) (x 3 13)
          have b58810 := hb (x 3 13)
          have b58811 := hb (x 3 3 && x 3 13)
          clear * - r58809 b58810 b58811 d58800
          omega
        have d58812 : (x 3 5).toNat = 0 := by
          have r58813 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
          have b58814 := hb (x 3 5)
          have b58815 := hb (x 3 13)
          clear * - r58813 b58814 b58815 d58800
          omega
        have d58816 : (x 3 5 && x 3 9).toNat = 0 := by
          have r58817 := hand1 (x 3 5) (x 3 9)
          have b58818 := hb (x 3 5)
          have b58819 := hb (x 3 5 && x 3 9)
          clear * - r58817 b58818 b58819 d58812
          omega
        have d58820 : (x 1 3).toNat = 0 := by
          have r58821 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e58822 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
          have e58823 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
          have b58824 := hb (x 1 3)
          have b58825 := hb (x 2 2)
          have b58826 := hb (x 3 13)
          have b58827 := hb (x 4 12)
          clear * - r58821 e58822 e58823 b58824 b58825 b58826 b58827 d58780 d58800 d58752
          omega
        have d58828 : (x 1 11).toNat = 0 := by
          have r58829 : (x 1 11).toNat ≤ (x 1 3).toNat := himp _ _ (hp11 1)
          have b58830 := hb (x 1 3)
          have b58831 := hb (x 1 11)
          clear * - r58829 b58830 b58831 d58820
          omega
        have d58832 : (x 1 7 && x 1 11).toNat = 0 := by
          have r58833 := hand2 (x 1 7) (x 1 11)
          have b58834 := hb (x 1 11)
          have b58835 := hb (x 1 7 && x 1 11)
          clear * - r58833 b58834 b58835 d58828
          omega
        have d58836 : (x 2 2 && x 2 12).toNat = 1 := by
          have r58837 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b58838 := hb (x (-1) 5)
          have b58839 := hb (x 4 10)
          have b58840 := hb (x 3 1 && x 3 11)
          have b58841 := hb (x 2 2 && x 2 12)
          have b58842 := hb (x 1 3 && x 1 13)
          have b58843 := hb (x 0 4 && x 0 14)
          clear * - r58837 b58838 b58839 b58840 b58841 b58842 b58843 d58212 d58248 d58768 d58741 d58168
          omega
        have d58844 : (x 2 12).toNat = 1 := by
          have r58845 := hand2 (x 2 2) (x 2 12)
          have b58846 := hb (x 2 12)
          have b58847 := hb (x 2 2 && x 2 12)
          clear * - r58845 b58846 b58847 d58836
          omega
        have d58848 : (x (-1) 3).toNat = 0 := by
          have r58849 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e58850 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
          have e58851 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
          have b58852 := hb (x (-1) 3)
          have b58853 := hb (x 0 2)
          have b58854 := hb (x 1 13)
          have b58855 := hb (x 2 12)
          clear * - r58849 e58850 e58851 b58852 b58853 b58854 b58855 d58844 d58764 f58657
          omega
        have d58856 : (x (-1) 11).toNat = 0 := by
          have r58857 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
          have b58858 := hb (x (-1) 3)
          have b58859 := hb (x (-1) 11)
          clear * - r58857 b58858 b58859 d58848
          omega
        have d58860 : (x (-1) 2 && x (-1) 11).toNat = 0 := by
          have r58861 := hand2 (x (-1) 2) (x (-1) 11)
          have b58862 := hb (x (-1) 11)
          have b58863 := hb (x (-1) 2 && x (-1) 11)
          clear * - r58861 b58862 b58863 d58856
          omega
        cases h58864 : x 0 5
        · have f58865 : (x 0 5).toNat = 0 := by rw [h58864]; rfl
          have d58866 : (x 2 3 && x 2 13).toNat = 1 := by
            have r58867 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b58868 := hb (x 0 5)
            have b58869 := hb (x 5 10)
            have b58870 := hb (x 4 1 && x 4 11)
            have b58871 := hb (x 3 2 && x 3 12)
            have b58872 := hb (x 2 3 && x 2 13)
            have b58873 := hb (x 1 4 && x 1 14)
            clear * - r58867 b58868 b58869 b58870 b58871 b58872 b58873 g8 g21 d58695 d58636 f58865
            omega
          have d58874 : (x 2 3).toNat = 1 := by
            have r58875 := hand1 (x 2 3) (x 2 13)
            have b58876 := hb (x 2 3)
            have b58877 := hb (x 2 3 && x 2 13)
            clear * - r58875 b58876 b58877 d58866
            omega
          have d58878 : (x 5 12).toNat = 0 := by
            have r58879 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e58880 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e58881 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b58882 := hb (x 2 3)
            have b58883 := hb (x 3 2)
            have b58884 := hb (x 4 13)
            have b58885 := hb (x 5 12)
            clear * - r58879 e58880 e58881 b58882 b58883 b58884 b58885 d58691 d58874
            omega
          have d58886 : (x 5 1 && x 5 12).toNat = 0 := by
            have r58887 := hand2 (x 5 1) (x 5 12)
            have b58888 := hb (x 5 12)
            have b58889 := hb (x 5 1 && x 5 12)
            clear * - r58887 b58888 b58889 d58878
            omega
          have d58890 : (x 5 2 && x 5 12).toNat = 0 := by
            have r58891 := hand2 (x 5 2) (x 5 12)
            have b58892 := hb (x 5 12)
            have b58893 := hb (x 5 2 && x 5 12)
            clear * - r58891 b58892 b58893 d58878
            omega
          have d58894 : (x 5 4).toNat = 0 := by
            have r58895 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
            have b58896 := hb (x 5 4)
            have b58897 := hb (x 5 12)
            clear * - r58895 b58896 b58897 d58878
            omega
          have d58898 : (x 4 13).toNat = 0 := by
            have r58899 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e58900 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
            have e58901 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
            have b58902 := hb (x 2 3)
            have b58903 := hb (x 3 2)
            have b58904 := hb (x 4 13)
            have b58905 := hb (x 5 12)
            clear * - r58899 e58900 e58901 b58902 b58903 b58904 b58905 d58878 d58691 d58874
            omega
          have d58906 : (x 4 2 && x 4 13).toNat = 0 := by
            have r58907 := hand2 (x 4 2) (x 4 13)
            have b58908 := hb (x 4 13)
            have b58909 := hb (x 4 2 && x 4 13)
            clear * - r58907 b58908 b58909 d58898
            omega
          have d58910 : (x 6 11).toNat = 1 := by
            have r58911 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b58912 := hb (x 2 4)
            have b58913 := hb (x 6 11)
            have b58914 := hb (x 5 1 && x 5 12)
            have b58915 := hb (x 4 2 && x 4 13)
            have b58916 := hb (x 3 3 && x 3 14)
            clear * - r58911 b58912 b58913 b58914 b58915 b58916 d58886 d58906 d58679 d58256
            omega
          have d58917 : (x 6 3).toNat = 1 := by
            have r58918 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
            have b58919 := hb (x 6 3)
            have b58920 := hb (x 6 11)
            clear * - r58918 b58919 b58920 d58910
            omega
          have d58921 : (x 9 12).toNat = 0 := by
            have r58922 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e58923 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e58924 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b58925 := hb (x 6 3)
            have b58926 := hb (x 7 2)
            have b58927 := hb (x 8 13)
            have b58928 := hb (x 9 12)
            clear * - r58922 e58923 e58924 b58925 b58926 b58927 b58928 d58917
            omega
          have d58929 : (x 9 4).toNat = 0 := by
            have r58930 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
            have b58931 := hb (x 9 4)
            have b58932 := hb (x 9 12)
            clear * - r58930 b58931 b58932 d58921
            omega
          have d58933 : (x 9 4 && x 9 14).toNat = 0 := by
            have r58934 := hand1 (x 9 4) (x 9 14)
            have b58935 := hb (x 9 4)
            have b58936 := hb (x 9 4 && x 9 14)
            clear * - r58934 b58935 b58936 d58929
            omega
          have d58937 : (x 8 13).toNat = 0 := by
            have r58938 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e58939 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e58940 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b58941 := hb (x 6 3)
            have b58942 := hb (x 7 2)
            have b58943 := hb (x 8 13)
            have b58944 := hb (x 9 12)
            clear * - r58938 e58939 e58940 b58941 b58942 b58943 b58944 d58921 d58917
            omega
          have d58945 : (x 8 5).toNat = 0 := by
            have r58946 : (x 8 5).toNat ≤ (x 8 13).toNat := himp _ _ (hp5 8)
            have b58947 := hb (x 8 5)
            have b58948 := hb (x 8 13)
            clear * - r58946 b58947 b58948 d58937
            omega
          have d58949 : (x 7 2).toNat = 0 := by
            have r58950 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e58951 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
            have e58952 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
            have b58953 := hb (x 6 3)
            have b58954 := hb (x 7 2)
            have b58955 := hb (x 8 13)
            have b58956 := hb (x 9 12)
            clear * - r58950 e58951 e58952 b58953 b58954 b58955 b58956 d58921 d58937 d58917
            omega
          have d58957 : (x 7 2 && x 7 7).toNat = 0 := by
            have r58958 := hand1 (x 7 2) (x 7 7)
            have b58959 := hb (x 7 2)
            have b58960 := hb (x 7 2 && x 7 7)
            clear * - r58958 b58959 b58960 d58949
            omega
          have d58961 : (x 7 10).toNat = 0 := by
            have r58962 : (x 7 10).toNat ≤ (x 7 2).toNat := himp _ _ (hp10 7)
            have b58963 := hb (x 7 2)
            have b58964 := hb (x 7 10)
            clear * - r58962 b58963 b58964 d58949
            omega
          have d58965 : (x 4 3 && x 4 13).toNat = 0 := by
            have r58966 := hand2 (x 4 3) (x 4 13)
            have b58967 := hb (x 4 13)
            have b58968 := hb (x 4 3 && x 4 13)
            clear * - r58966 b58967 b58968 d58898
            omega
          have d58969 : (x 6 1 && x 6 11).toNat = 1 := by
            have r58970 : 1 ≤ (x 7 10).toNat + (x 6 1 && x 6 11).toNat + (x 5 2 && x 5 12).toNat + (x 4 3 && x 4 13).toNat + (x 3 4 && x 3 14).toNat + (x 2 5).toNat := by have q := hcov10 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b58971 := hb (x 2 5)
            have b58972 := hb (x 7 10)
            have b58973 := hb (x 6 1 && x 6 11)
            have b58974 := hb (x 5 2 && x 5 12)
            have b58975 := hb (x 4 3 && x 4 13)
            have b58976 := hb (x 3 4 && x 3 14)
            clear * - r58970 b58971 b58972 b58973 b58974 b58975 b58976 d58961 d58890 d58965 g22 g6
            omega
          have d58977 : (x 6 1).toNat = 1 := by
            have r58978 := hand1 (x 6 1) (x 6 11)
            have b58979 := hb (x 6 1)
            have b58980 := hb (x 6 1 && x 6 11)
            clear * - r58978 b58979 b58980 d58969
            omega
          have d58981 : (x 7 14).toNat = 0 := by
            have r58982 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b58983 := hb (x 6 1)
            have b58984 := hb (x 7 14)
            clear * - r58982 b58983 b58984 d58977
            omega
          have d58985 : (x 7 1 && x 7 14).toNat = 0 := by
            have r58986 := hand2 (x 7 1) (x 7 14)
            have b58987 := hb (x 7 14)
            have b58988 := hb (x 7 1 && x 7 14)
            clear * - r58986 b58987 b58988 d58981
            omega
          have d58989 : (x 6 2).toNat = 1 := by
            have r58990 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b58991 := hb (x 6 2)
            have b58992 := hb (x 8 13)
            have b58993 := hb (x 7 1 && x 7 14)
            clear * - r58990 b58991 b58992 b58993 d58937 d58985
            omega
          have d58994 : (x 6 14).toNat = 1 := by
            have r58995 : (x 6 2).toNat ≤ (x 6 14).toNat := himp _ _ (hp2 6)
            have b58996 := hb (x 6 2)
            have b58997 := hb (x 6 14)
            clear * - r58995 b58996 b58997 d58989
            omega
          have d58998 : (x 5 1).toNat = 0 := by
            have r58999 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b59000 := hb (x 5 1)
            have b59001 := hb (x 6 14)
            clear * - r58999 b59000 b59001 d58994
            omega
          have d59002 : (x 5 1 && x 5 11).toNat = 0 := by
            have r59003 := hand1 (x 5 1) (x 5 11)
            have b59004 := hb (x 5 1)
            have b59005 := hb (x 5 1 && x 5 11)
            clear * - r59003 b59004 b59005 d58998
            omega
          have d59006 : (x 6 10).toNat = 1 := by
            have r59007 : 1 ≤ (x 6 10).toNat + (x 5 1 && x 5 11).toNat + (x 4 2 && x 4 12).toNat + (x 3 3 && x 3 13).toNat + (x 2 4 && x 2 14).toNat + (x 1 5).toNat := by have q := hcov10 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b59008 := hb (x 1 5)
            have b59009 := hb (x 6 10)
            have b59010 := hb (x 5 1 && x 5 11)
            have b59011 := hb (x 4 2 && x 4 12)
            have b59012 := hb (x 3 3 && x 3 13)
            have b59013 := hb (x 2 4 && x 2 14)
            clear * - r59007 b59008 b59009 b59010 b59011 b59012 b59013 d59002 d58788 d58808 d58272 d58276
            omega
          have d59014 : (x 5 13).toNat = 0 := by
            have r59015 : (x 5 13).toNat ≤ (x 5 1).toNat := himp _ _ (hp13 5)
            have b59016 := hb (x 5 1)
            have b59017 := hb (x 5 13)
            clear * - r59015 b59016 b59017 d58998
            omega
          have d59018 : (x 4 1 && x 4 14).toNat = 1 := by
            have r59019 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b59020 := hb (x 3 2)
            have b59021 := hb (x 5 13)
            have b59022 := hb (x 4 1 && x 4 14)
            clear * - r59019 b59020 b59021 b59022 d59014 d58691
            omega
          have d59023 : (x 4 1).toNat = 1 := by
            have r59024 := hand1 (x 4 1) (x 4 14)
            have b59025 := hb (x 4 1)
            have b59026 := hb (x 4 1 && x 4 14)
            clear * - r59024 b59025 b59026 d59018
            omega
          have d59027 : (x 5 14).toNat = 0 := by
            have r59028 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b59029 := hb (x 4 1)
            have b59030 := hb (x 5 14)
            clear * - r59028 b59029 b59030 d59023
            omega
          have d59031 : (x 5 6).toNat = 0 := by
            have r59032 : (x 5 6).toNat ≤ (x 5 14).toNat := himp _ _ (hp6 5)
            have b59033 := hb (x 5 6)
            have b59034 := hb (x 5 14)
            clear * - r59032 b59033 b59034 d59027
            omega
          have d59035 : (x 8 12).toNat = 0 := by
            have r59036 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59037 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e59038 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b59039 := hb (x 5 3)
            have b59040 := hb (x 6 2)
            have b59041 := hb (x 7 13)
            have b59042 := hb (x 8 12)
            clear * - r59036 e59037 e59038 b59039 b59040 b59041 b59042 d58989
            omega
          have d59043 : (x 8 3 && x 8 12).toNat = 0 := by
            have r59044 := hand2 (x 8 3) (x 8 12)
            have b59045 := hb (x 8 12)
            have b59046 := hb (x 8 3 && x 8 12)
            clear * - r59044 b59045 b59046 d59035
            omega
          have d59047 : (x 8 4).toNat = 0 := by
            have r59048 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
            have b59049 := hb (x 8 4)
            have b59050 := hb (x 8 12)
            clear * - r59048 b59049 b59050 d59035
            omega
          have d59051 : (x 7 13).toNat = 0 := by
            have r59052 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59053 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e59054 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b59055 := hb (x 5 3)
            have b59056 := hb (x 6 2)
            have b59057 := hb (x 7 13)
            have b59058 := hb (x 8 12)
            clear * - r59052 e59053 e59054 b59055 b59056 b59057 b59058 d59035 d58989
            omega
          have d59059 : (x 7 4 && x 7 13).toNat = 0 := by
            have r59060 := hand2 (x 7 4) (x 7 13)
            have b59061 := hb (x 7 13)
            have b59062 := hb (x 7 4 && x 7 13)
            clear * - r59060 b59061 b59062 d59051
            omega
          have d59063 : (x 7 5).toNat = 0 := by
            have r59064 : (x 7 5).toNat ≤ (x 7 13).toNat := himp _ _ (hp5 7)
            have b59065 := hb (x 7 5)
            have b59066 := hb (x 7 13)
            clear * - r59064 b59065 b59066 d59051
            omega
          have d59067 : (x 5 3).toNat = 0 := by
            have r59068 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59069 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
            have e59070 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
            have b59071 := hb (x 5 3)
            have b59072 := hb (x 6 2)
            have b59073 := hb (x 7 13)
            have b59074 := hb (x 8 12)
            clear * - r59068 e59069 e59070 b59071 b59072 b59073 b59074 d59035 d59051 d58989
            omega
          have d59075 : (x 5 3 && x 5 7).toNat = 0 := by
            have r59076 := hand1 (x 5 3) (x 5 7)
            have b59077 := hb (x 5 3)
            have b59078 := hb (x 5 3 && x 5 7)
            clear * - r59076 b59077 b59078 d59067
            omega
          have d59079 : (x 5 11).toNat = 0 := by
            have r59080 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
            have b59081 := hb (x 5 3)
            have b59082 := hb (x 5 11)
            clear * - r59080 b59081 b59082 d59067
            omega
          have d59083 : (x 4 5).toNat = 0 := by
            have r59084 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
            have b59085 := hb (x 4 5)
            have b59086 := hb (x 4 13)
            clear * - r59084 b59085 b59086 d58898
            omega
          have d59087 : (x 9 8).toNat = 0 := by
            have r59088 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59089 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e59090 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e59091 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e59092 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e59093 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e59094 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b59095 := hb (x 2 7)
            have b59096 := hb (x 3 6)
            have b59097 := hb (x 4 5)
            have b59098 := hb (x 5 4)
            have b59099 := hb (x 6 11)
            have b59100 := hb (x 7 10)
            have b59101 := hb (x 8 9)
            have b59102 := hb (x 9 8)
            clear * - r59088 e59089 e59090 e59091 e59092 e59093 e59094 b59095 b59096 b59097 b59098 b59099 b59100 b59101 b59102 d58961 d58910 d58894 d59083 d58683
            omega
          have d59103 : (x 8 9).toNat = 0 := by
            have r59104 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59105 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e59106 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e59107 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e59108 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e59109 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e59110 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b59111 := hb (x 2 7)
            have b59112 := hb (x 3 6)
            have b59113 := hb (x 4 5)
            have b59114 := hb (x 5 4)
            have b59115 := hb (x 6 11)
            have b59116 := hb (x 7 10)
            have b59117 := hb (x 8 9)
            have b59118 := hb (x 9 8)
            clear * - r59104 e59105 e59106 e59107 e59108 e59109 e59110 b59111 b59112 b59113 b59114 b59115 b59116 b59117 b59118 d59087 d58961 d58910 d58894 d59083 d58683
            omega
          have d59119 : (x 2 7).toNat = 0 := by
            have r59120 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59121 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
            have e59122 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
            have e59123 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
            have e59124 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
            have e59125 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
            have e59126 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
            have b59127 := hb (x 2 7)
            have b59128 := hb (x 3 6)
            have b59129 := hb (x 4 5)
            have b59130 := hb (x 5 4)
            have b59131 := hb (x 6 11)
            have b59132 := hb (x 7 10)
            have b59133 := hb (x 8 9)
            have b59134 := hb (x 9 8)
            clear * - r59120 e59121 e59122 e59123 e59124 e59125 e59126 b59127 b59128 b59129 b59130 b59131 b59132 b59133 b59134 d59087 d59103 d58961 d58910 d58894 d59083 d58683
            omega
          have d59135 : (x 2 7 && x 2 13).toNat = 0 := by
            have r59136 := hand1 (x 2 7) (x 2 13)
            have b59137 := hb (x 2 7)
            have b59138 := hb (x 2 7 && x 2 13)
            clear * - r59136 b59137 b59138 d59119
            omega
          have d59139 : (x 2 7 && x 2 12).toNat = 0 := by
            have r59140 := hand1 (x 2 7) (x 2 12)
            have b59141 := hb (x 2 7)
            have b59142 := hb (x 2 7 && x 2 12)
            clear * - r59140 b59141 b59142 d59119
            omega
          have d59143 : (x 8 8).toNat = 0 := by
            have r59144 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59145 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e59146 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e59147 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e59148 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e59149 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e59150 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b59151 := hb (x 1 7)
            have b59152 := hb (x 2 6)
            have b59153 := hb (x 3 5)
            have b59154 := hb (x 4 4)
            have b59155 := hb (x 5 11)
            have b59156 := hb (x 6 10)
            have b59157 := hb (x 7 9)
            have b59158 := hb (x 8 8)
            clear * - r59144 e59145 e59146 e59147 e59148 e59149 e59150 b59151 b59152 b59153 b59154 b59155 b59156 b59157 b59158 d59006 d59079 d58792 d58812
            omega
          have d59159 : (x 7 9).toNat = 0 := by
            have r59160 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59161 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e59162 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e59163 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e59164 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e59165 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e59166 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b59167 := hb (x 1 7)
            have b59168 := hb (x 2 6)
            have b59169 := hb (x 3 5)
            have b59170 := hb (x 4 4)
            have b59171 := hb (x 5 11)
            have b59172 := hb (x 6 10)
            have b59173 := hb (x 7 9)
            have b59174 := hb (x 8 8)
            clear * - r59160 e59161 e59162 e59163 e59164 e59165 e59166 b59167 b59168 b59169 b59170 b59171 b59172 b59173 b59174 d59143 d59006 d59079 d58792 d58812
            omega
          have d59175 : (x 2 6).toNat = 0 := by
            have r59176 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59177 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
            have e59178 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
            have e59179 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
            have e59180 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
            have e59181 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
            have e59182 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
            have b59183 := hb (x 1 7)
            have b59184 := hb (x 2 6)
            have b59185 := hb (x 3 5)
            have b59186 := hb (x 4 4)
            have b59187 := hb (x 5 11)
            have b59188 := hb (x 6 10)
            have b59189 := hb (x 7 9)
            have b59190 := hb (x 8 8)
            clear * - r59176 e59177 e59178 e59179 e59180 e59181 e59182 b59183 b59184 b59185 b59186 b59187 b59188 b59189 b59190 d59143 d59159 d59006 d59079 d58792 d58812
            omega
          have d59191 : (x 2 6 && x 2 10).toNat = 0 := by
            have r59192 := hand1 (x 2 6) (x 2 10)
            have b59193 := hb (x 2 6)
            have b59194 := hb (x 2 6 && x 2 10)
            clear * - r59192 b59193 b59194 d59175
            omega
          have r59195 : (x 10 1).toNat + (x 9 2).toNat + (x 8 3).toNat + (x 7 4).toNat + (x 6 5).toNat + (x 5 6).toNat + (x 4 7).toNat + (x 3 8).toNat + (x 2 9).toNat + (x 1 10).toNat + (x 0 11).toNat + (x (-1) 12).toNat + (x (-2) 13).toNat + (x (-3) 14).toNat = 3 := by have q := hcount 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r59196 : (x 1 8).toNat + (x 0 1 && x 0 9).toNat + (x (-1) 2 && x (-1) 10).toNat + (x (-2) 3 && x (-2) 11).toNat + (x (-3) 4 && x (-3) 12).toNat + (x (-4) 5 && x (-4) 13).toNat + (x (-5) 6 && x (-5) 14).toNat + (x (-6) 7).toNat = 1 := by have q := hd8 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e59197 : (x 0 1 && x 0 9).toNat = (x 0 9).toNat := handr _ _ (fun h => hp9 0 (h))
          have e59198 : (x (-1) 2 && x (-1) 10).toNat = (x (-1) 10).toNat := handr _ _ (fun h => hp10 (-1) (h))
          have e59199 : (x (-2) 3 && x (-2) 11).toNat = (x (-2) 11).toNat := handr _ _ (fun h => hp11 (-2) (h))
          have e59200 : (x (-3) 4 && x (-3) 12).toNat = (x (-3) 4).toNat := handl _ _ (fun h => hp4 (-3) (h))
          have e59201 : (x (-4) 5 && x (-4) 13).toNat = (x (-4) 5).toNat := handl _ _ (fun h => hp5 (-4) (h))
          have e59202 : (x (-5) 6 && x (-5) 14).toNat = (x (-5) 6).toNat := handl _ _ (fun h => hp6 (-5) (h))
          have r59203 : (x 12 8).toNat + (x 11 1 && x 11 9).toNat + (x 10 2 && x 10 10).toNat + (x 9 3 && x 9 11).toNat + (x 8 4 && x 8 12).toNat + (x 7 5 && x 7 13).toNat + (x 6 6 && x 6 14).toNat + (x 5 7).toNat = 1 := by have q := hd8 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e59204 : (x 11 1 && x 11 9).toNat = (x 11 9).toNat := handr _ _ (fun h => hp9 11 (h))
          have e59205 : (x 10 2 && x 10 10).toNat = (x 10 10).toNat := handr _ _ (fun h => hp10 10 (h))
          have e59206 : (x 9 3 && x 9 11).toNat = (x 9 11).toNat := handr _ _ (fun h => hp11 9 (h))
          have e59207 : (x 8 4 && x 8 12).toNat = (x 8 4).toNat := handl _ _ (fun h => hp4 8 (h))
          have e59208 : (x 7 5 && x 7 13).toNat = (x 7 5).toNat := handl _ _ (fun h => hp5 7 (h))
          have e59209 : (x 6 6 && x 6 14).toNat = (x 6 6).toNat := handl _ _ (fun h => hp6 6 (h))
          have r59210 : (x 14 8).toNat + (x 13 1 && x 13 9).toNat + (x 12 2 && x 12 10).toNat + (x 11 3 && x 11 11).toNat + (x 10 4 && x 10 12).toNat + (x 9 5 && x 9 13).toNat + (x 8 6 && x 8 14).toNat + (x 7 7).toNat = 1 := by have q := hd8 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e59211 : (x 13 1 && x 13 9).toNat = (x 13 9).toNat := handr _ _ (fun h => hp9 13 (h))
          have e59212 : (x 12 2 && x 12 10).toNat = (x 12 10).toNat := handr _ _ (fun h => hp10 12 (h))
          have e59213 : (x 11 3 && x 11 11).toNat = (x 11 11).toNat := handr _ _ (fun h => hp11 11 (h))
          have e59214 : (x 10 4 && x 10 12).toNat = (x 10 4).toNat := handl _ _ (fun h => hp4 10 (h))
          have e59215 : (x 9 5 && x 9 13).toNat = (x 9 5).toNat := handl _ _ (fun h => hp5 9 (h))
          have e59216 : (x 8 6 && x 8 14).toNat = (x 8 6).toNat := handl _ _ (fun h => hp6 8 (h))
          have r59217 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e59218 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
          have e59219 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
          have e59220 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
          have e59221 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
          have e59222 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
          have e59223 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
          have r59224 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e59225 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e59226 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have r59227 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e59228 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
          have e59229 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
          have r59230 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e59231 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e59232 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have r59233 : 1 ≤ (x 8 4).toNat + (x 7 1 && x 7 5).toNat + (x 6 2 && x 6 6).toNat + (x 5 3 && x 5 7).toNat + (x 4 4 && x 4 8).toNat + (x 3 5 && x 3 9).toNat + (x 2 6 && x 2 10).toNat + (x 1 7 && x 1 11).toNat + (x 0 8 && x 0 12).toNat + (x (-1) 9 && x (-1) 13).toNat + (x (-2) 10 && x (-2) 14).toNat + (x (-3) 11).toNat := by have q := hcov4 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e59234 : (x 7 1 && x 7 5).toNat = (x 7 5).toNat := handr _ _ (fun h => hp13 7 (hp5 7 (h)))
          have e59235 : (x (-2) 10 && x (-2) 14).toNat = (x (-2) 10).toNat := handl _ _ (fun h => hp2 (-2) (hp10 (-2) (h)))
          have r59236 : 1 ≤ (x 11 4).toNat + (x 10 1 && x 10 5).toNat + (x 9 2 && x 9 6).toNat + (x 8 3 && x 8 7).toNat + (x 7 4 && x 7 8).toNat + (x 6 5 && x 6 9).toNat + (x 5 6 && x 5 10).toNat + (x 4 7 && x 4 11).toNat + (x 3 8 && x 3 12).toNat + (x 2 9 && x 2 13).toNat + (x 1 10 && x 1 14).toNat + (x 0 11).toNat := by have q := hcov4 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e59237 : (x 10 1 && x 10 5).toNat = (x 10 5).toNat := handr _ _ (fun h => hp13 10 (hp5 10 (h)))
          have e59238 : (x 1 10 && x 1 14).toNat = (x 1 10).toNat := handl _ _ (fun h => hp2 1 (hp10 1 (h)))
          have r59239 : 1 ≤ (x 9 5).toNat + (x 8 1 && x 8 6).toNat + (x 7 2 && x 7 7).toNat + (x 6 3 && x 6 8).toNat + (x 5 4 && x 5 9).toNat + (x 4 5 && x 4 10).toNat + (x 3 6 && x 3 11).toNat + (x 2 7 && x 2 12).toNat + (x 1 8 && x 1 13).toNat + (x 0 9 && x 0 14).toNat + (x (-1) 10).toNat := by have q := hcov5 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r59240 : 1 ≤ (x 9 6).toNat + (x 8 1 && x 8 7).toNat + (x 7 2 && x 7 8).toNat + (x 6 3 && x 6 9).toNat + (x 5 4 && x 5 10).toNat + (x 4 5 && x 4 11).toNat + (x 3 6 && x 3 12).toNat + (x 2 7 && x 2 13).toNat + (x 1 8 && x 1 14).toNat + (x 0 9).toNat := by have q := hcov6 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r59241 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r59242 : 1 ≤ (x 1 9).toNat + (x 0 1 && x 0 10).toNat + (x (-1) 2 && x (-1) 11).toNat + (x (-2) 3 && x (-2) 12).toNat + (x (-3) 4 && x (-3) 13).toNat + (x (-4) 5 && x (-4) 14).toNat + (x (-5) 6).toNat := by have q := hcov9 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r59243 : 1 ≤ (x 11 9).toNat + (x 10 1 && x 10 10).toNat + (x 9 2 && x 9 11).toNat + (x 8 3 && x 8 12).toNat + (x 7 4 && x 7 13).toNat + (x 6 5 && x 6 14).toNat + (x 5 6).toNat := by have q := hcov9 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r59244 : 1 ≤ (x 13 10).toNat + (x 12 1 && x 12 11).toNat + (x 11 2 && x 11 12).toNat + (x 10 3 && x 10 13).toNat + (x 9 4 && x 9 14).toNat + (x 8 5).toNat := by have q := hcov10 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r59245 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r59246 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r59247 : 1 ≤ (x 0 13).toNat + (x (-1) 1 && x (-1) 14).toNat + (x (-2) 2).toNat := by have q := hcov13 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r59248 := hand2 (x 6 2) (x 6 6)
          have r59249 := hand2 (x 0 8) (x 0 12)
          have r59250 := hand1 (x 9 2) (x 9 6)
          have r59251 := hand1 (x 8 3) (x 8 7)
          have r59252 := hand1 (x 2 9) (x 2 13)
          have r59253 := hand2 (x 8 1) (x 8 6)
          have r59254 := hand2 (x 8 1) (x 8 7)
          have r59255 := hand2 (x (-2) 2) (x (-2) 11)
          have r59256 := hand1 (x (-3) 3) (x (-3) 12)
          have r59257 := hand1 (x (-2) 3) (x (-2) 12)
          have r59258 := hand1 (x (-3) 4) (x (-3) 13)
          have r59259 := hand1 (x (-4) 5) (x (-4) 14)
          have r59260 := hand2 (x 10 1) (x 10 10)
          have r59261 := hand2 (x 9 2) (x 9 11)
          have r59262 := hand1 (x 6 5) (x 6 14)
          have r59263 := hand2 (x 12 1) (x 12 11)
          have r59264 := hand2 (x 11 2) (x 11 12)
          have r59265 := hand2 (x 10 3) (x 10 13)
          have r59266 := hand2 (x (-2) 2) (x (-2) 13)
          have r59267 := hand2 (x (-3) 3) (x (-3) 14)
          have r59268 := hand1 (x 10 1) (x 10 12)
          have r59269 := hand1 (x 9 2) (x 9 13)
          have r59270 := hand1 (x 8 3) (x 8 14)
          linarith only [r59195, r59196, e59197, e59198, e59199, e59200, e59201, e59202, r59203, e59204, e59205, e59206, e59207, e59208, e59209, r59210, e59211, e59212, e59213, e59214, e59215, e59216, r59217, e59218, e59219, e59220, e59221, e59222, e59223, r59224, e59225, e59226, r59227, e59228, e59229, r59230, e59231, e59232, r59233, e59234, e59235, r59236, e59237, e59238, r59239, r59240, r59241, r59242, r59243, r59244, r59245, r59246, r59247, r59248, r59249, r59250, r59251, r59252, r59253, r59254, r59255, r59256, r59257, r59258, r59259, r59260, r59261, r59262, r59263, r59264, r59265, r59266, r59267, r59268, r59269, r59270, g0, g1, g2, g3, d58164, g5, d58731, d58776, d58652, d59031, d59063, d59047, d58945, d59075, d58796, d58816, d59191, d58832, g9, g10, g11, g12, g13, d58715, d58957, d58188, d58208, d58228, d58252, d59139, d58772, g14, g15, g16, g17, g18, d58687, d59135, d58640, d58160, g19, g20, d58662, d58860, d59043, d59059, d58933, d58156, d58152]
        · have f59392 : (x 0 5).toNat = 1 := by rw [h58864]; rfl
          have d59393 : (x 0 13).toNat = 1 := by
            have r59394 : (x 0 5).toNat ≤ (x 0 13).toNat := himp _ _ (hp5 0)
            have b59395 := hb (x 0 5)
            have b59396 := hb (x 0 13)
            clear * - r59394 b59395 b59396 f59392
            omega
          have d59397 : (x 1 12).toNat = 0 := by
            have r59398 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59399 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e59400 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b59401 := hb (x (-2) 3)
            have b59402 := hb (x (-1) 2)
            have b59403 := hb (x 0 13)
            have b59404 := hb (x 1 12)
            clear * - r59398 e59399 e59400 b59401 b59402 b59403 b59404 d59393
            omega
          have d59405 : (x 1 4).toNat = 0 := by
            have r59406 : (x 1 4).toNat ≤ (x 1 12).toNat := himp _ _ (hp4 1)
            have b59407 := hb (x 1 4)
            have b59408 := hb (x 1 12)
            clear * - r59406 b59407 b59408 d59397
            omega
          have d59409 : (x (-1) 2).toNat = 0 := by
            have r59410 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59411 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e59412 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b59413 := hb (x (-2) 3)
            have b59414 := hb (x (-1) 2)
            have b59415 := hb (x 0 13)
            have b59416 := hb (x 1 12)
            clear * - r59410 e59411 e59412 b59413 b59414 b59415 b59416 d59397 d59393
            omega
          have d59417 : (x (-1) 2 && x (-1) 12).toNat = 0 := by
            have r59418 := hand1 (x (-1) 2) (x (-1) 12)
            have b59419 := hb (x (-1) 2)
            have b59420 := hb (x (-1) 2 && x (-1) 12)
            clear * - r59418 b59419 b59420 d59409
            omega
          have d59421 : (x (-2) 3).toNat = 0 := by
            have r59422 : (x 1 12).toNat + (x 0 1 && x 0 13).toNat + (x (-1) 2 && x (-1) 14).toNat + (x (-2) 3).toNat = 1 := by have q := hd12 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59423 : (x 0 1 && x 0 13).toNat = (x 0 13).toNat := handr _ _ (fun h => hp13 0 (h))
            have e59424 : (x (-1) 2 && x (-1) 14).toNat = (x (-1) 2).toNat := handl _ _ (fun h => hp2 (-1) (h))
            have b59425 := hb (x (-2) 3)
            have b59426 := hb (x (-1) 2)
            have b59427 := hb (x 0 13)
            have b59428 := hb (x 1 12)
            clear * - r59422 e59423 e59424 b59425 b59426 b59427 b59428 d59397 d59393 d59409
            omega
          have d59429 : (x (-2) 3 && x (-2) 13).toNat = 0 := by
            have r59430 := hand1 (x (-2) 3) (x (-2) 13)
            have b59431 := hb (x (-2) 3)
            have b59432 := hb (x (-2) 3 && x (-2) 13)
            clear * - r59430 b59431 b59432 d59421
            omega
          have d59433 : (x (-2) 11).toNat = 0 := by
            have r59434 : (x (-2) 11).toNat ≤ (x (-2) 3).toNat := himp _ _ (hp11 (-2))
            have b59435 := hb (x (-2) 3)
            have b59436 := hb (x (-2) 11)
            clear * - r59434 b59435 b59436 d59421
            omega
          have d59437 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
            have r59438 := hand2 (x (-2) 2) (x (-2) 11)
            have b59439 := hb (x (-2) 11)
            have b59440 := hb (x (-2) 2 && x (-2) 11)
            clear * - r59438 b59439 b59440 d59433
            omega
          have d59441 : (x (-3) 3 && x (-3) 12).toNat = 1 := by
            have r59442 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b59443 := hb (x (-6) 6)
            have b59444 := hb (x 0 9)
            have b59445 := hb (x (-1) 1 && x (-1) 10)
            have b59446 := hb (x (-2) 2 && x (-2) 11)
            have b59447 := hb (x (-3) 3 && x (-3) 12)
            have b59448 := hb (x (-4) 4 && x (-4) 13)
            have b59449 := hb (x (-5) 5 && x (-5) 14)
            clear * - r59442 b59443 b59444 b59445 b59446 b59447 b59448 b59449 g5 d58160 d59437 g19 g20 g0
            omega
          have d59450 : (x (-3) 12).toNat = 1 := by
            have r59451 := hand2 (x (-3) 3) (x (-3) 12)
            have b59452 := hb (x (-3) 12)
            have b59453 := hb (x (-3) 3 && x (-3) 12)
            clear * - r59451 b59452 b59453 d59441
            omega
          have d59454 : (x (-4) 13).toNat = 0 := by
            have r59455 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59456 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e59457 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b59458 := hb (x (-6) 3)
            have b59459 := hb (x (-5) 2)
            have b59460 := hb (x (-4) 13)
            have b59461 := hb (x (-3) 12)
            clear * - r59455 e59456 e59457 b59458 b59459 b59460 b59461 d59450
            omega
          have d59462 : (x (-4) 5).toNat = 0 := by
            have r59463 : (x (-4) 5).toNat ≤ (x (-4) 13).toNat := himp _ _ (hp5 (-4))
            have b59464 := hb (x (-4) 5)
            have b59465 := hb (x (-4) 13)
            clear * - r59463 b59464 b59465 d59454
            omega
          have d59466 : (x (-3) 4 && x (-3) 14).toNat = 1 := by
            have r59467 : 1 ≤ (x 1 10).toNat + (x 0 1 && x 0 11).toNat + (x (-1) 2 && x (-1) 12).toNat + (x (-2) 3 && x (-2) 13).toNat + (x (-3) 4 && x (-3) 14).toNat + (x (-4) 5).toNat := by have q := hcov10 1; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b59468 := hb (x (-4) 5)
            have b59469 := hb (x 1 10)
            have b59470 := hb (x 0 1 && x 0 11)
            have b59471 := hb (x (-1) 2 && x (-1) 12)
            have b59472 := hb (x (-2) 3 && x (-2) 13)
            have b59473 := hb (x (-3) 4 && x (-3) 14)
            clear * - r59467 b59468 b59469 b59470 b59471 b59472 b59473 d58652 d58735 d59417 d59429 d59462
            omega
          have d59474 : (x (-3) 14).toNat = 1 := by
            have r59475 := hand2 (x (-3) 4) (x (-3) 14)
            have b59476 := hb (x (-3) 14)
            have b59477 := hb (x (-3) 4 && x (-3) 14)
            clear * - r59475 b59476 b59477 d59466
            omega
          have d59478 : (x (-4) 1).toNat = 0 := by
            have r59479 : (x (-3) 14).toNat + (x (-4) 1).toNat = 1 := by have q := hd14 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b59480 := hb (x (-4) 1)
            have b59481 := hb (x (-3) 14)
            clear * - r59479 b59480 b59481 d59474
            omega
          have d59482 : (x (-4) 1 && x (-4) 14).toNat = 0 := by
            have r59483 := hand1 (x (-4) 1) (x (-4) 14)
            have b59484 := hb (x (-4) 1)
            have b59485 := hb (x (-4) 1 && x (-4) 14)
            clear * - r59483 b59484 b59485 d59478
            omega
          have d59486 : (x (-5) 2).toNat = 0 := by
            have r59487 : (x (-3) 12).toNat + (x (-4) 1 && x (-4) 13).toNat + (x (-5) 2 && x (-5) 14).toNat + (x (-6) 3).toNat = 1 := by have q := hd12 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59488 : (x (-4) 1 && x (-4) 13).toNat = (x (-4) 13).toNat := handr _ _ (fun h => hp13 (-4) (h))
            have e59489 : (x (-5) 2 && x (-5) 14).toNat = (x (-5) 2).toNat := handl _ _ (fun h => hp2 (-5) (h))
            have b59490 := hb (x (-6) 3)
            have b59491 := hb (x (-5) 2)
            have b59492 := hb (x (-4) 13)
            have b59493 := hb (x (-3) 12)
            clear * - r59487 e59488 e59489 b59490 b59491 b59492 b59493 d59450 d59454
            omega
          have d59494 : (x (-3) 13).toNat = 1 := by
            have r59495 : 1 ≤ (x (-3) 13).toNat + (x (-4) 1 && x (-4) 14).toNat + (x (-5) 2).toNat := by have q := hcov13 (-3); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b59496 := hb (x (-5) 2)
            have b59497 := hb (x (-3) 13)
            have b59498 := hb (x (-4) 1 && x (-4) 14)
            clear * - r59495 b59496 b59497 b59498 d59482 d59486
            omega
          have d59499 : (x (-3) 1).toNat = 1 := by
            have r59500 : (x (-3) 13).toNat ≤ (x (-3) 1).toNat := himp _ _ (hp13 (-3))
            have b59501 := hb (x (-3) 1)
            have b59502 := hb (x (-3) 13)
            clear * - r59500 b59501 b59502 d59494
            omega
          have d59503 : (x (-2) 14).toNat = 0 := by
            have r59504 : (x (-2) 14).toNat + (x (-3) 1).toNat = 1 := by have q := hd14 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b59505 := hb (x (-3) 1)
            have b59506 := hb (x (-2) 14)
            clear * - r59504 b59505 b59506 d59499
            omega
          have d59507 : (x (-2) 1 && x (-2) 14).toNat = 0 := by
            have r59508 := hand2 (x (-2) 1) (x (-2) 14)
            have b59509 := hb (x (-2) 14)
            have b59510 := hb (x (-2) 1 && x (-2) 14)
            clear * - r59508 b59509 b59510 d59503
            omega
          have d59511 : (x (-3) 2).toNat = 1 := by
            have r59512 : 1 ≤ (x (-1) 13).toNat + (x (-2) 1 && x (-2) 14).toNat + (x (-3) 2).toNat := by have q := hcov13 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b59513 := hb (x (-3) 2)
            have b59514 := hb (x (-1) 13)
            have b59515 := hb (x (-2) 1 && x (-2) 14)
            clear * - r59512 b59513 b59514 b59515 d58164 d59507
            omega
          have d59516 : (x (-1) 12).toNat = 0 := by
            have r59517 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59518 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e59519 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b59520 := hb (x (-4) 3)
            have b59521 := hb (x (-3) 2)
            have b59522 := hb (x (-2) 13)
            have b59523 := hb (x (-1) 12)
            clear * - r59517 e59518 e59519 b59520 b59521 b59522 b59523 d59511
            omega
          have d59524 : (x (-1) 4).toNat = 0 := by
            have r59525 : (x (-1) 4).toNat ≤ (x (-1) 12).toNat := himp _ _ (hp4 (-1))
            have b59526 := hb (x (-1) 4)
            have b59527 := hb (x (-1) 12)
            clear * - r59525 b59526 b59527 d59516
            omega
          have d59528 : (x (-1) 4 && x (-1) 14).toNat = 0 := by
            have r59529 := hand1 (x (-1) 4) (x (-1) 14)
            have b59530 := hb (x (-1) 4)
            have b59531 := hb (x (-1) 4 && x (-1) 14)
            clear * - r59529 b59530 b59531 d59524
            omega
          have d59532 : (x (-2) 13).toNat = 0 := by
            have r59533 : (x (-1) 12).toNat + (x (-2) 1 && x (-2) 13).toNat + (x (-3) 2 && x (-3) 14).toNat + (x (-4) 3).toNat = 1 := by have q := hd12 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e59534 : (x (-2) 1 && x (-2) 13).toNat = (x (-2) 13).toNat := handr _ _ (fun h => hp13 (-2) (h))
            have e59535 : (x (-3) 2 && x (-3) 14).toNat = (x (-3) 2).toNat := handl _ _ (fun h => hp2 (-3) (h))
            have b59536 := hb (x (-4) 3)
            have b59537 := hb (x (-3) 2)
            have b59538 := hb (x (-2) 13)
            have b59539 := hb (x (-1) 12)
            clear * - r59533 e59534 e59535 b59536 b59537 b59538 b59539 d59516 d59511
            omega
          have d59540 : (x (-2) 5).toNat = 0 := by
            have r59541 : (x (-2) 5).toNat ≤ (x (-2) 13).toNat := himp _ _ (hp5 (-2))
            have b59542 := hb (x (-2) 5)
            have b59543 := hb (x (-2) 13)
            clear * - r59541 b59542 b59543 d59532
            omega
          have d59544 : (x 2 1 && x 2 11).toNat = 1 := by
            have r59545 : 1 ≤ (x 3 10).toNat + (x 2 1 && x 2 11).toNat + (x 1 2 && x 1 12).toNat + (x 0 3 && x 0 13).toNat + (x (-1) 4 && x (-1) 14).toNat + (x (-2) 5).toNat := by have q := hcov10 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have b59546 := hb (x (-2) 5)
            have b59547 := hb (x 3 10)
            have b59548 := hb (x 2 1 && x 2 11)
            have b59549 := hb (x 1 2 && x 1 12)
            have b59550 := hb (x 0 3 && x 0 13)
            have b59551 := hb (x (-1) 4 && x (-1) 14)
            clear * - r59545 b59546 b59547 b59548 b59549 b59550 b59551 d58699 d58648 d58727 d59528 d59540
            omega
          have d59552 : (x 2 11).toNat = 1 := by
            have r59553 := hand2 (x 2 1) (x 2 11)
            have b59554 := hb (x 2 11)
            have b59555 := hb (x 2 1 && x 2 11)
            clear * - r59553 b59554 b59555 d59544
            omega
          have r59556 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e59557 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
          have e59558 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
          have e59559 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
          have e59560 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
          have e59561 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
          have e59562 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
          have b59563 := hb (x (-2) 7)
          have b59564 := hb (x (-1) 6)
          have b59565 := hb (x 0 5)
          have b59566 := hb (x 1 4)
          have b59567 := hb (x 2 11)
          have b59568 := hb (x 3 10)
          have b59569 := hb (x 4 9)
          have b59570 := hb (x 5 8)
          linarith only [r59556, e59557, e59558, e59559, e59560, e59561, e59562, b59563, b59564, b59565, b59566, b59567, b59568, b59569, b59570, d58699, d59552, d59405, f59392]
      · have f59571 : (x 0 4).toNat = 1 := by rw [h58739]; rfl
        have d59572 : (x 0 12).toNat = 1 := by
          have r59573 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
          have b59574 := hb (x 0 4)
          have b59575 := hb (x 0 12)
          clear * - r59573 b59574 b59575 f59571
          omega
        have d59576 : (x (-2) 2).toNat = 0 := by
          have r59577 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e59578 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e59579 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b59580 := hb (x (-3) 3)
          have b59581 := hb (x (-2) 2)
          have b59582 := hb (x (-1) 13)
          have b59583 := hb (x 0 12)
          clear * - r59577 e59578 e59579 b59580 b59581 b59582 b59583 d59572 d58164
          omega
        have d59584 : (x (-2) 2 && x (-2) 13).toNat = 0 := by
          have r59585 := hand1 (x (-2) 2) (x (-2) 13)
          have b59586 := hb (x (-2) 2)
          have b59587 := hb (x (-2) 2 && x (-2) 13)
          clear * - r59585 b59586 b59587 d59576
          omega
        have d59588 : (x (-3) 3).toNat = 0 := by
          have r59589 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e59590 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
          have e59591 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
          have b59592 := hb (x (-3) 3)
          have b59593 := hb (x (-2) 2)
          have b59594 := hb (x (-1) 13)
          have b59595 := hb (x 0 12)
          clear * - r59589 e59590 e59591 b59592 b59593 b59594 b59595 d59572 d58164 d59576
          omega
        have d59596 : (x (-3) 3 && x (-3) 14).toNat = 0 := by
          have r59597 := hand1 (x (-3) 3) (x (-3) 14)
          have b59598 := hb (x (-3) 3)
          have b59599 := hb (x (-3) 3 && x (-3) 14)
          clear * - r59597 b59598 b59599 d59588
          omega
        have r59600 : 1 ≤ (x 0 11).toNat + (x (-1) 1 && x (-1) 12).toNat + (x (-2) 2 && x (-2) 13).toNat + (x (-3) 3 && x (-3) 14).toNat + (x (-4) 4).toNat := by have q := hcov11 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b59601 := hb (x (-4) 4)
        have b59602 := hb (x 0 11)
        have b59603 := hb (x (-1) 1 && x (-1) 12)
        have b59604 := hb (x (-2) 2 && x (-2) 13)
        have b59605 := hb (x (-3) 3 && x (-3) 14)
        linarith only [r59600, b59601, b59602, b59603, b59604, b59605, d58731, d58156, d59584, d59596, g1]
    · have f59606 : (x 0 2).toNat = 1 := by rw [h58656]; rfl
      have d59607 : (x 2 12).toNat = 0 := by
        have r59608 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e59609 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e59610 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b59611 := hb (x (-1) 3)
        have b59612 := hb (x 0 2)
        have b59613 := hb (x 1 13)
        have b59614 := hb (x 2 12)
        clear * - r59608 e59609 e59610 b59611 b59612 b59613 b59614 f59606
        omega
      have d59615 : (x 2 2 && x 2 12).toNat = 0 := by
        have r59616 := hand2 (x 2 2) (x 2 12)
        have b59617 := hb (x 2 12)
        have b59618 := hb (x 2 2 && x 2 12)
        clear * - r59616 b59617 b59618 d59607
        omega
      have d59619 : (x 1 13).toNat = 0 := by
        have r59620 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e59621 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e59622 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b59623 := hb (x (-1) 3)
        have b59624 := hb (x 0 2)
        have b59625 := hb (x 1 13)
        have b59626 := hb (x 2 12)
        clear * - r59620 e59621 e59622 b59623 b59624 b59625 b59626 d59607 f59606
        omega
      have d59627 : (x 1 3 && x 1 13).toNat = 0 := by
        have r59628 := hand2 (x 1 3) (x 1 13)
        have b59629 := hb (x 1 13)
        have b59630 := hb (x 1 3 && x 1 13)
        clear * - r59628 b59629 b59630 d59619
        omega
      have d59631 : (x 0 4 && x 0 14).toNat = 1 := by
        have r59632 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b59633 := hb (x (-1) 5)
        have b59634 := hb (x 4 10)
        have b59635 := hb (x 3 1 && x 3 11)
        have b59636 := hb (x 2 2 && x 2 12)
        have b59637 := hb (x 1 3 && x 1 13)
        have b59638 := hb (x 0 4 && x 0 14)
        clear * - r59632 b59633 b59634 b59635 b59636 b59637 b59638 d58212 d58248 d59615 d59627 d58168
        omega
      have d59639 : (x 0 4).toNat = 1 := by
        have r59640 := hand1 (x 0 4) (x 0 14)
        have b59641 := hb (x 0 4)
        have b59642 := hb (x 0 4 && x 0 14)
        clear * - r59640 b59641 b59642 d59631
        omega
      have d59643 : (x 0 12).toNat = 1 := by
        have r59644 : (x 0 4).toNat ≤ (x 0 12).toNat := himp _ _ (hp4 0)
        have b59645 := hb (x 0 4)
        have b59646 := hb (x 0 12)
        clear * - r59644 b59645 b59646 d59639
        omega
      have d59647 : (x (-2) 2).toNat = 0 := by
        have r59648 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e59649 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e59650 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b59651 := hb (x (-3) 3)
        have b59652 := hb (x (-2) 2)
        have b59653 := hb (x (-1) 13)
        have b59654 := hb (x 0 12)
        clear * - r59648 e59649 e59650 b59651 b59652 b59653 b59654 d59643 d58164
        omega
      have d59655 : (x (-2) 2 && x (-2) 11).toNat = 0 := by
        have r59656 := hand1 (x (-2) 2) (x (-2) 11)
        have b59657 := hb (x (-2) 2)
        have b59658 := hb (x (-2) 2 && x (-2) 11)
        clear * - r59656 b59657 b59658 d59647
        omega
      have d59659 : (x (-3) 3).toNat = 0 := by
        have r59660 : (x 0 12).toNat + (x (-1) 1 && x (-1) 13).toNat + (x (-2) 2 && x (-2) 14).toNat + (x (-3) 3).toNat = 1 := by have q := hd12 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e59661 : (x (-1) 1 && x (-1) 13).toNat = (x (-1) 13).toNat := handr _ _ (fun h => hp13 (-1) (h))
        have e59662 : (x (-2) 2 && x (-2) 14).toNat = (x (-2) 2).toNat := handl _ _ (fun h => hp2 (-2) (h))
        have b59663 := hb (x (-3) 3)
        have b59664 := hb (x (-2) 2)
        have b59665 := hb (x (-1) 13)
        have b59666 := hb (x 0 12)
        clear * - r59660 e59661 e59662 b59663 b59664 b59665 b59666 d59643 d58164 d59647
        omega
      have d59667 : (x (-3) 3 && x (-3) 12).toNat = 0 := by
        have r59668 := hand1 (x (-3) 3) (x (-3) 12)
        have b59669 := hb (x (-3) 3)
        have b59670 := hb (x (-3) 3 && x (-3) 12)
        clear * - r59668 b59669 b59670 d59659
        omega
      have r59671 : 1 ≤ (x 0 9).toNat + (x (-1) 1 && x (-1) 10).toNat + (x (-2) 2 && x (-2) 11).toNat + (x (-3) 3 && x (-3) 12).toNat + (x (-4) 4 && x (-4) 13).toNat + (x (-5) 5 && x (-5) 14).toNat + (x (-6) 6).toNat := by have q := hcov9 0; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b59672 := hb (x (-6) 6)
      have b59673 := hb (x 0 9)
      have b59674 := hb (x (-1) 1 && x (-1) 10)
      have b59675 := hb (x (-2) 2 && x (-2) 11)
      have b59676 := hb (x (-3) 3 && x (-3) 12)
      have b59677 := hb (x (-4) 4 && x (-4) 13)
      have b59678 := hb (x (-5) 5 && x (-5) 14)
      linarith only [r59671, b59672, b59673, b59674, b59675, b59676, b59677, b59678, g5, d58160, d59655, d59667, g19, g20, g0]

theorem cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a11 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-6) 6).toNat = 0)
    (g1 : (x (-4) 4).toNat = 0)
    (g2 : (x (-3) 11).toNat = 0)
    (g3 : (x (-2) 10).toNat = 0)
    (g4 : (x 0 6).toNat = 1)
    (g5 : (x 0 9).toNat = 0)
    (g6 : (x 2 5).toNat = 0)
    (g7 : (x 4 11).toNat = 0)
    (g8 : (x 5 10).toNat = 0)
    (g9 : (x (-1) 9 && x (-1) 13).toNat = 0)
    (g10 : (x 7 4 && x 7 8).toNat = 0)
    (g11 : (x 6 5 && x 6 9).toNat = 0)
    (g12 : (x 5 6 && x 5 10).toNat = 0)
    (g13 : (x 4 7 && x 4 11).toNat = 0)
    (g14 : (x 0 9 && x 0 14).toNat = 0)
    (g15 : (x 7 2 && x 7 8).toNat = 0)
    (g16 : (x 6 3 && x 6 9).toNat = 0)
    (g17 : (x 5 4 && x 5 10).toNat = 0)
    (g18 : (x 4 5 && x 4 11).toNat = 0)
    (g19 : (x (-4) 4 && x (-4) 13).toNat = 0)
    (g20 : (x (-5) 5 && x (-5) 14).toNat = 0)
    (g21 : (x 4 1 && x 4 11).toNat = 0)
    (g22 : (x 3 4 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_eight_iff_nine_core_a11_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22
