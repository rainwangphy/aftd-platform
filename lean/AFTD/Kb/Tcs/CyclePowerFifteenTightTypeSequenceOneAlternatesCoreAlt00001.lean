import AFTD.Prelude

/-!
# cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00001

Topic: combinatorics   Node: 88b346cf187f

Provenance: helper lemma. Window step for simple_graph_cycle_power_fifteen_cover_five_local_periods (research thread RT-1, open case k = 15 of OP-205, arXiv:2610.15635). Experiments 5738 and 5937 and the follow-up pairing/alternation run: on the integer window [-32, 32] the layer-free system refutes both mismatches by a case-split tree with unit propagation and LP-infeasible leaves.

One branch of the window refutation behind cycle_power_fifteen_tight_type_sequence_one_alternates_core: under the layer-free tight-cover constraints for k = 15 and 15 fixed bits of the class-type sequence near position 0, the constraints are contradictory. Its module also proves the sibling branches cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000101, cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt0000011.
-/

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00000101 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-2) 5).toNat = 0)
    (g1 : (x (-1) 3).toNat = 1)
    (g2 : (x (-1) 5).toNat = 0)
    (g3 : (x 0 2).toNat = 0)
    (g4 : (x 0 6).toNat = 0)
    (g5 : (x 0 11).toNat = 0)
    (g6 : (x 0 14).toNat = 0)
    (g7 : (x 1 5).toNat = 0)
    (g8 : (x 1 10).toNat = 0)
    (g9 : (x 1 13).toNat = 0)
    (g10 : (x 1 14).toNat = 1)
    (g11 : (x 2 13).toNat = 1)
    (g12 : (x 3 2).toNat = 0)
    (g13 : (x 3 4).toNat = 0)
    (g14 : (x 3 6).toNat = 0)
    (g15 : (x 3 12).toNat = 0)
    (g16 : (x 3 14).toNat = 0)
    (g17 : (x 3 11 && x 3 12).toNat = 0)
    (g18 : (x 1 13 && x 1 14).toNat = 0)
    (g19 : (x 3 8 && x 3 12).toNat = 0)
    (g20 : (x 3 3 && x 3 12).toNat = 0)
    (g21 : (x 1 5 && x 1 14).toNat = 0)
    (g22 : (x 1 3 && x 1 13).toNat = 0)
    (g23 : (x 0 4 && x 0 14).toNat = 0)
    (g24 : (x 1 2 && x 1 13).toNat = 0)
    (g25 : (x 0 3 && x 0 14).toNat = 0)
    (g26 : (x 3 3 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d18153 : (x 2 12).toNat = 0 := by
    have r18154 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18155 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
    have e18156 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
    have b18157 := hb (x (-1) 3)
    have b18158 := hb (x 0 2)
    have b18159 := hb (x 1 13)
    have b18160 := hb (x 2 12)
    clear * - r18154 e18155 e18156 b18157 b18158 b18159 b18160 g9 g3 g1
    omega
  have d18161 : (x 2 1 && x 2 12).toNat = 0 := by
    have r18162 := hand2 (x 2 1) (x 2 12)
    have b18163 := hb (x 2 12)
    have b18164 := hb (x 2 1 && x 2 12)
    clear * - r18162 b18163 b18164 d18153
    omega
  have d18165 : (x 2 2 && x 2 12).toNat = 0 := by
    have r18166 := hand2 (x 2 2) (x 2 12)
    have b18167 := hb (x 2 12)
    have b18168 := hb (x 2 2 && x 2 12)
    clear * - r18166 b18167 b18168 d18153
    omega
  have d18169 : (x 2 12 && x 2 13).toNat = 0 := by
    have r18170 := hand1 (x 2 12) (x 2 13)
    have b18171 := hb (x 2 12)
    have b18172 := hb (x 2 12 && x 2 13)
    clear * - r18170 b18171 b18172 d18153
    omega
  have d18173 : (x 2 4).toNat = 0 := by
    have r18174 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
    have b18175 := hb (x 2 4)
    have b18176 := hb (x 2 12)
    clear * - r18174 b18175 b18176 d18153
    omega
  have d18177 : (x 2 4 && x 2 13).toNat = 0 := by
    have r18178 := hand1 (x 2 4) (x 2 13)
    have b18179 := hb (x 2 4)
    have b18180 := hb (x 2 4 && x 2 13)
    clear * - r18178 b18179 b18180 d18173
    omega
  cases h18181 : x (-1) 4
  · have f18182 : (x (-1) 4).toNat = 0 := by rw [h18181]; rfl
    have d18183 : (x 3 11).toNat = 1 := by
      have r18184 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18185 := hb (x (-1) 4)
      have b18186 := hb (x 3 11)
      have b18187 := hb (x 2 1 && x 2 12)
      have b18188 := hb (x 1 2 && x 1 13)
      have b18189 := hb (x 0 3 && x 0 14)
      clear * - r18184 b18185 b18186 b18187 b18188 b18189 d18161 g24 g25 f18182
      omega
    have d18190 : (x 3 3).toNat = 1 := by
      have r18191 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
      have b18192 := hb (x 3 3)
      have b18193 := hb (x 3 11)
      clear * - r18191 b18192 b18193 d18183
      omega
    have d18194 : (x 6 12).toNat = 0 := by
      have r18195 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18196 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e18197 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b18198 := hb (x 3 3)
      have b18199 := hb (x 4 2)
      have b18200 := hb (x 5 13)
      have b18201 := hb (x 6 12)
      clear * - r18195 e18196 e18197 b18198 b18199 b18200 b18201 d18190
      omega
    have d18202 : (x 6 1 && x 6 12).toNat = 0 := by
      have r18203 := hand2 (x 6 1) (x 6 12)
      have b18204 := hb (x 6 12)
      have b18205 := hb (x 6 1 && x 6 12)
      clear * - r18203 b18204 b18205 d18194
      omega
    have d18206 : (x 6 4).toNat = 0 := by
      have r18207 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
      have b18208 := hb (x 6 4)
      have b18209 := hb (x 6 12)
      clear * - r18207 b18208 b18209 d18194
      omega
    have d18210 : (x 5 13).toNat = 0 := by
      have r18211 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18212 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e18213 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b18214 := hb (x 3 3)
      have b18215 := hb (x 4 2)
      have b18216 := hb (x 5 13)
      have b18217 := hb (x 6 12)
      clear * - r18211 e18212 e18213 b18214 b18215 b18216 b18217 d18194 d18190
      omega
    have d18218 : (x 5 2 && x 5 13).toNat = 0 := by
      have r18219 := hand2 (x 5 2) (x 5 13)
      have b18220 := hb (x 5 13)
      have b18221 := hb (x 5 2 && x 5 13)
      clear * - r18219 b18220 b18221 d18210
      omega
    have d18222 : (x 4 1 && x 4 14).toNat = 1 := by
      have r18223 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18224 := hb (x 3 2)
      have b18225 := hb (x 5 13)
      have b18226 := hb (x 4 1 && x 4 14)
      clear * - r18223 b18224 b18225 b18226 d18210 g12
      omega
    have d18227 : (x 4 1).toNat = 1 := by
      have r18228 := hand1 (x 4 1) (x 4 14)
      have b18229 := hb (x 4 1)
      have b18230 := hb (x 4 1 && x 4 14)
      clear * - r18228 b18229 b18230 d18222
      omega
    have d18231 : (x 5 14).toNat = 0 := by
      have r18232 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18233 := hb (x 4 1)
      have b18234 := hb (x 5 14)
      clear * - r18232 b18233 b18234 d18227
      omega
    have d18235 : (x 5 1 && x 5 14).toNat = 0 := by
      have r18236 := hand2 (x 5 1) (x 5 14)
      have b18237 := hb (x 5 14)
      have b18238 := hb (x 5 1 && x 5 14)
      clear * - r18236 b18237 b18238 d18231
      omega
    have d18239 : (x 5 2).toNat = 0 := by
      have r18240 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
      have b18241 := hb (x 5 2)
      have b18242 := hb (x 5 14)
      clear * - r18240 b18241 b18242 d18231
      omega
    have d18243 : (x 4 2).toNat = 0 := by
      have r18244 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18245 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
      have e18246 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
      have b18247 := hb (x 3 3)
      have b18248 := hb (x 4 2)
      have b18249 := hb (x 5 13)
      have b18250 := hb (x 6 12)
      clear * - r18244 e18245 e18246 b18247 b18248 b18249 b18250 d18194 d18210 d18190
      omega
    have d18251 : (x 4 2 && x 4 13).toNat = 0 := by
      have r18252 := hand1 (x 4 2) (x 4 13)
      have b18253 := hb (x 4 2)
      have b18254 := hb (x 4 2 && x 4 13)
      clear * - r18252 b18253 b18254 d18243
      omega
    have d18255 : (x 6 13).toNat = 1 := by
      have r18256 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18257 := hb (x 4 2)
      have b18258 := hb (x 6 13)
      have b18259 := hb (x 5 1 && x 5 14)
      clear * - r18256 b18257 b18258 b18259 d18235 d18243
      omega
    have d18260 : (x 6 1).toNat = 1 := by
      have r18261 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
      have b18262 := hb (x 6 1)
      have b18263 := hb (x 6 13)
      clear * - r18261 b18262 b18263 d18255
      omega
    have d18264 : (x 7 14).toNat = 0 := by
      have r18265 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18266 := hb (x 6 1)
      have b18267 := hb (x 7 14)
      clear * - r18265 b18266 b18267 d18260
      omega
    have d18268 : (x 7 3 && x 7 14).toNat = 0 := by
      have r18269 := hand2 (x 7 3) (x 7 14)
      have b18270 := hb (x 7 14)
      have b18271 := hb (x 7 3 && x 7 14)
      clear * - r18269 b18270 b18271 d18264
      omega
    have d18272 : (x 7 2).toNat = 0 := by
      have r18273 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
      have b18274 := hb (x 7 2)
      have b18275 := hb (x 7 14)
      clear * - r18273 b18274 b18275 d18264
      omega
    have d18276 : (x 7 12).toNat = 0 := by
      have r18277 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18278 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e18279 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b18280 := hb (x 4 3)
      have b18281 := hb (x 5 2)
      have b18282 := hb (x 6 13)
      have b18283 := hb (x 7 12)
      clear * - r18277 e18278 e18279 b18280 b18281 b18282 b18283 d18255 d18239
      omega
    have d18284 : (x 7 4).toNat = 0 := by
      have r18285 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
      have b18286 := hb (x 7 4)
      have b18287 := hb (x 7 12)
      clear * - r18285 b18286 b18287 d18276
      omega
    have d18288 : (x 4 3).toNat = 0 := by
      have r18289 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18290 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
      have e18291 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
      have b18292 := hb (x 4 3)
      have b18293 := hb (x 5 2)
      have b18294 := hb (x 6 13)
      have b18295 := hb (x 7 12)
      clear * - r18289 e18290 e18291 b18292 b18293 b18294 b18295 d18276 d18255 d18239
      omega
    have d18296 : (x 4 3 && x 4 14).toNat = 0 := by
      have r18297 := hand1 (x 4 3) (x 4 14)
      have b18298 := hb (x 4 3)
      have b18299 := hb (x 4 3 && x 4 14)
      clear * - r18297 b18298 b18299 d18288
      omega
    have d18300 : (x 7 11).toNat = 1 := by
      have r18301 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18302 := hb (x 3 4)
      have b18303 := hb (x 7 11)
      have b18304 := hb (x 6 1 && x 6 12)
      have b18305 := hb (x 5 2 && x 5 13)
      have b18306 := hb (x 4 3 && x 4 14)
      clear * - r18301 b18302 b18303 b18304 b18305 b18306 d18202 d18218 d18296 g13
      omega
    have d18307 : (x 7 3).toNat = 1 := by
      have r18308 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
      have b18309 := hb (x 7 3)
      have b18310 := hb (x 7 11)
      clear * - r18308 b18309 b18310 d18300
      omega
    have d18311 : (x 10 12).toNat = 0 := by
      have r18312 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18313 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e18314 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b18315 := hb (x 7 3)
      have b18316 := hb (x 8 2)
      have b18317 := hb (x 9 13)
      have b18318 := hb (x 10 12)
      clear * - r18312 e18313 e18314 b18315 b18316 b18317 b18318 d18307
      omega
    have d18319 : (x 10 1 && x 10 12).toNat = 0 := by
      have r18320 := hand2 (x 10 1) (x 10 12)
      have b18321 := hb (x 10 12)
      have b18322 := hb (x 10 1 && x 10 12)
      clear * - r18320 b18321 b18322 d18311
      omega
    have d18323 : (x 10 4).toNat = 0 := by
      have r18324 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
      have b18325 := hb (x 10 4)
      have b18326 := hb (x 10 12)
      clear * - r18324 b18325 b18326 d18311
      omega
    have d18327 : (x 9 13).toNat = 0 := by
      have r18328 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18329 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e18330 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b18331 := hb (x 7 3)
      have b18332 := hb (x 8 2)
      have b18333 := hb (x 9 13)
      have b18334 := hb (x 10 12)
      clear * - r18328 e18329 e18330 b18331 b18332 b18333 b18334 d18311 d18307
      omega
    have d18335 : (x 9 2 && x 9 13).toNat = 0 := by
      have r18336 := hand2 (x 9 2) (x 9 13)
      have b18337 := hb (x 9 13)
      have b18338 := hb (x 9 2 && x 9 13)
      clear * - r18336 b18337 b18338 d18327
      omega
    have d18339 : (x 8 1 && x 8 14).toNat = 1 := by
      have r18340 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18341 := hb (x 7 2)
      have b18342 := hb (x 9 13)
      have b18343 := hb (x 8 1 && x 8 14)
      clear * - r18340 b18341 b18342 b18343 d18327 d18272
      omega
    have d18344 : (x 8 14).toNat = 1 := by
      have r18345 := hand2 (x 8 1) (x 8 14)
      have b18346 := hb (x 8 14)
      have b18347 := hb (x 8 1 && x 8 14)
      clear * - r18345 b18346 b18347 d18339
      omega
    have d18348 : (x 7 1).toNat = 0 := by
      have r18349 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18350 := hb (x 7 1)
      have b18351 := hb (x 8 14)
      clear * - r18349 b18350 b18351 d18344
      omega
    have d18352 : (x 7 13).toNat = 0 := by
      have r18353 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
      have b18354 := hb (x 7 1)
      have b18355 := hb (x 7 13)
      clear * - r18353 b18354 b18355 d18348
      omega
    have d18356 : (x 6 1 && x 6 14).toNat = 1 := by
      have r18357 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18358 := hb (x 5 2)
      have b18359 := hb (x 7 13)
      have b18360 := hb (x 6 1 && x 6 14)
      clear * - r18357 b18358 b18359 b18360 d18352 d18239
      omega
    have d18361 : (x 6 14).toNat = 1 := by
      have r18362 := hand2 (x 6 1) (x 6 14)
      have b18363 := hb (x 6 14)
      have b18364 := hb (x 6 1 && x 6 14)
      clear * - r18362 b18363 b18364 d18356
      omega
    have d18365 : (x 5 1).toNat = 0 := by
      have r18366 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18367 := hb (x 5 1)
      have b18368 := hb (x 6 14)
      clear * - r18366 b18367 b18368 d18361
      omega
    have d18369 : (x 5 1 && x 5 12).toNat = 0 := by
      have r18370 := hand1 (x 5 1) (x 5 12)
      have b18371 := hb (x 5 1)
      have b18372 := hb (x 5 1 && x 5 12)
      clear * - r18370 b18371 b18372 d18365
      omega
    have d18373 : (x 6 11).toNat = 1 := by
      have r18374 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18375 := hb (x 2 4)
      have b18376 := hb (x 6 11)
      have b18377 := hb (x 5 1 && x 5 12)
      have b18378 := hb (x 4 2 && x 4 13)
      have b18379 := hb (x 3 3 && x 3 14)
      clear * - r18374 b18375 b18376 b18377 b18378 b18379 d18369 d18251 g26 d18173
      omega
    have d18380 : (x 6 3).toNat = 1 := by
      have r18381 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
      have b18382 := hb (x 6 3)
      have b18383 := hb (x 6 11)
      clear * - r18381 b18382 b18383 d18373
      omega
    have d18384 : (x 9 12).toNat = 0 := by
      have r18385 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18386 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e18387 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b18388 := hb (x 6 3)
      have b18389 := hb (x 7 2)
      have b18390 := hb (x 8 13)
      have b18391 := hb (x 9 12)
      clear * - r18385 e18386 e18387 b18388 b18389 b18390 b18391 d18272 d18380
      omega
    have d18392 : (x 9 1 && x 9 12).toNat = 0 := by
      have r18393 := hand2 (x 9 1) (x 9 12)
      have b18394 := hb (x 9 12)
      have b18395 := hb (x 9 1 && x 9 12)
      clear * - r18393 b18394 b18395 d18384
      omega
    have d18396 : (x 8 13).toNat = 0 := by
      have r18397 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18398 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
      have e18399 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
      have b18400 := hb (x 6 3)
      have b18401 := hb (x 7 2)
      have b18402 := hb (x 8 13)
      have b18403 := hb (x 9 12)
      clear * - r18397 e18398 e18399 b18400 b18401 b18402 b18403 d18384 d18272 d18380
      omega
    have d18404 : (x 8 2 && x 8 13).toNat = 0 := by
      have r18405 := hand2 (x 8 2) (x 8 13)
      have b18406 := hb (x 8 13)
      have b18407 := hb (x 8 2 && x 8 13)
      clear * - r18405 b18406 b18407 d18396
      omega
    have d18408 : (x 10 11).toNat = 1 := by
      have r18409 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18410 := hb (x 6 4)
      have b18411 := hb (x 10 11)
      have b18412 := hb (x 9 1 && x 9 12)
      have b18413 := hb (x 8 2 && x 8 13)
      have b18414 := hb (x 7 3 && x 7 14)
      clear * - r18409 b18410 b18411 b18412 b18413 b18414 d18392 d18404 d18268 d18206
      omega
    have d18415 : (x 10 3).toNat = 1 := by
      have r18416 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
      have b18417 := hb (x 10 3)
      have b18418 := hb (x 10 11)
      clear * - r18416 b18417 b18418 d18408
      omega
    have d18419 : (x 13 12).toNat = 0 := by
      have r18420 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18421 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e18422 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b18423 := hb (x 10 3)
      have b18424 := hb (x 11 2)
      have b18425 := hb (x 12 13)
      have b18426 := hb (x 13 12)
      clear * - r18420 e18421 e18422 b18423 b18424 b18425 b18426 d18415
      omega
    have d18427 : (x 13 1 && x 13 12).toNat = 0 := by
      have r18428 := hand2 (x 13 1) (x 13 12)
      have b18429 := hb (x 13 12)
      have b18430 := hb (x 13 1 && x 13 12)
      clear * - r18428 b18429 b18430 d18419
      omega
    have d18431 : (x 12 13).toNat = 0 := by
      have r18432 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18433 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e18434 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b18435 := hb (x 10 3)
      have b18436 := hb (x 11 2)
      have b18437 := hb (x 12 13)
      have b18438 := hb (x 13 12)
      clear * - r18432 e18433 e18434 b18435 b18436 b18437 b18438 d18419 d18415
      omega
    have d18439 : (x 12 2 && x 12 13).toNat = 0 := by
      have r18440 := hand2 (x 12 2) (x 12 13)
      have b18441 := hb (x 12 13)
      have b18442 := hb (x 12 2 && x 12 13)
      clear * - r18440 b18441 b18442 d18431
      omega
    have d18443 : (x 11 2).toNat = 0 := by
      have r18444 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18445 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
      have e18446 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
      have b18447 := hb (x 10 3)
      have b18448 := hb (x 11 2)
      have b18449 := hb (x 12 13)
      have b18450 := hb (x 13 12)
      clear * - r18444 e18445 e18446 b18447 b18448 b18449 b18450 d18419 d18431 d18415
      omega
    have d18451 : (x 8 1).toNat = 1 := by
      have r18452 := hand1 (x 8 1) (x 8 14)
      have b18453 := hb (x 8 1)
      have b18454 := hb (x 8 1 && x 8 14)
      clear * - r18452 b18453 b18454 d18339
      omega
    have d18455 : (x 9 14).toNat = 0 := by
      have r18456 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18457 := hb (x 8 1)
      have b18458 := hb (x 9 14)
      clear * - r18456 b18457 b18458 d18451
      omega
    have d18459 : (x 9 1 && x 9 14).toNat = 0 := by
      have r18460 := hand2 (x 9 1) (x 9 14)
      have b18461 := hb (x 9 14)
      have b18462 := hb (x 9 1 && x 9 14)
      clear * - r18460 b18461 b18462 d18455
      omega
    have d18463 : (x 9 2).toNat = 0 := by
      have r18464 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
      have b18465 := hb (x 9 2)
      have b18466 := hb (x 9 14)
      clear * - r18464 b18465 b18466 d18455
      omega
    have d18467 : (x 8 2).toNat = 0 := by
      have r18468 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18469 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
      have e18470 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
      have b18471 := hb (x 7 3)
      have b18472 := hb (x 8 2)
      have b18473 := hb (x 9 13)
      have b18474 := hb (x 10 12)
      clear * - r18468 e18469 e18470 b18471 b18472 b18473 b18474 d18311 d18327 d18307
      omega
    have d18475 : (x 10 13).toNat = 1 := by
      have r18476 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18477 := hb (x 8 2)
      have b18478 := hb (x 10 13)
      have b18479 := hb (x 9 1 && x 9 14)
      clear * - r18476 b18477 b18478 b18479 d18459 d18467
      omega
    have d18480 : (x 10 1).toNat = 1 := by
      have r18481 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
      have b18482 := hb (x 10 1)
      have b18483 := hb (x 10 13)
      clear * - r18481 b18482 b18483 d18475
      omega
    have d18484 : (x 11 14).toNat = 0 := by
      have r18485 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18486 := hb (x 10 1)
      have b18487 := hb (x 11 14)
      clear * - r18485 b18486 b18487 d18480
      omega
    have d18488 : (x 11 1 && x 11 14).toNat = 0 := by
      have r18489 := hand2 (x 11 1) (x 11 14)
      have b18490 := hb (x 11 14)
      have b18491 := hb (x 11 1 && x 11 14)
      clear * - r18489 b18490 b18491 d18484
      omega
    have d18492 : (x 10 2).toNat = 1 := by
      have r18493 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18494 := hb (x 10 2)
      have b18495 := hb (x 12 13)
      have b18496 := hb (x 11 1 && x 11 14)
      clear * - r18493 b18494 b18495 b18496 d18431 d18488
      omega
    have d18497 : (x 12 12).toNat = 0 := by
      have r18498 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18499 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e18500 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b18501 := hb (x 9 3)
      have b18502 := hb (x 10 2)
      have b18503 := hb (x 11 13)
      have b18504 := hb (x 12 12)
      clear * - r18498 e18499 e18500 b18501 b18502 b18503 b18504 d18492
      omega
    have d18505 : (x 12 4).toNat = 0 := by
      have r18506 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
      have b18507 := hb (x 12 4)
      have b18508 := hb (x 12 12)
      clear * - r18506 b18507 b18508 d18497
      omega
    have d18509 : (x 12 4 && x 12 14).toNat = 0 := by
      have r18510 := hand1 (x 12 4) (x 12 14)
      have b18511 := hb (x 12 4)
      have b18512 := hb (x 12 4 && x 12 14)
      clear * - r18510 b18511 b18512 d18505
      omega
    have d18513 : (x 11 13).toNat = 0 := by
      have r18514 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18515 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
      have e18516 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
      have b18517 := hb (x 9 3)
      have b18518 := hb (x 10 2)
      have b18519 := hb (x 11 13)
      have b18520 := hb (x 12 12)
      clear * - r18514 e18515 e18516 b18517 b18518 b18519 b18520 d18497 d18492
      omega
    have d18521 : (x 11 5).toNat = 0 := by
      have r18522 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
      have b18523 := hb (x 11 5)
      have b18524 := hb (x 11 13)
      clear * - r18522 b18523 b18524 d18513
      omega
    have d18525 : (x 11 3 && x 11 14).toNat = 0 := by
      have r18526 := hand2 (x 11 3) (x 11 14)
      have b18527 := hb (x 11 14)
      have b18528 := hb (x 11 3 && x 11 14)
      clear * - r18526 b18527 b18528 d18484
      omega
    have d18529 : (x 14 11).toNat = 1 := by
      have r18530 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18531 := hb (x 10 4)
      have b18532 := hb (x 14 11)
      have b18533 := hb (x 13 1 && x 13 12)
      have b18534 := hb (x 12 2 && x 12 13)
      have b18535 := hb (x 11 3 && x 11 14)
      clear * - r18530 b18531 b18532 b18533 b18534 b18535 d18427 d18439 d18525 d18323
      omega
    have d18536 : (x 14 3).toNat = 1 := by
      have r18537 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
      have b18538 := hb (x 14 3)
      have b18539 := hb (x 14 11)
      clear * - r18537 b18538 b18539 d18529
      omega
    have d18540 : (x 17 12).toNat = 0 := by
      have r18541 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18542 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e18543 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b18544 := hb (x 14 3)
      have b18545 := hb (x 15 2)
      have b18546 := hb (x 16 13)
      have b18547 := hb (x 17 12)
      clear * - r18541 e18542 e18543 b18544 b18545 b18546 b18547 d18536
      omega
    have d18548 : (x 16 13).toNat = 0 := by
      have r18549 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18550 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e18551 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b18552 := hb (x 14 3)
      have b18553 := hb (x 15 2)
      have b18554 := hb (x 16 13)
      have b18555 := hb (x 17 12)
      clear * - r18549 e18550 e18551 b18552 b18553 b18554 b18555 d18540 d18536
      omega
    have d18556 : (x 15 2).toNat = 0 := by
      have r18557 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18558 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
      have e18559 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
      have b18560 := hb (x 14 3)
      have b18561 := hb (x 15 2)
      have b18562 := hb (x 16 13)
      have b18563 := hb (x 17 12)
      clear * - r18557 e18558 e18559 b18560 b18561 b18562 b18563 d18540 d18548 d18536
      omega
    have d18564 : (x 11 12).toNat = 0 := by
      have r18565 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18566 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e18567 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b18568 := hb (x 8 3)
      have b18569 := hb (x 9 2)
      have b18570 := hb (x 10 13)
      have b18571 := hb (x 11 12)
      clear * - r18565 e18566 e18567 b18568 b18569 b18570 b18571 d18475 d18463
      omega
    have d18572 : (x 11 4).toNat = 0 := by
      have r18573 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
      have b18574 := hb (x 11 4)
      have b18575 := hb (x 11 12)
      clear * - r18573 b18574 b18575 d18564
      omega
    have d18576 : (x 8 3).toNat = 0 := by
      have r18577 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18578 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
      have e18579 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
      have b18580 := hb (x 8 3)
      have b18581 := hb (x 9 2)
      have b18582 := hb (x 10 13)
      have b18583 := hb (x 11 12)
      clear * - r18577 e18578 e18579 b18580 b18581 b18582 b18583 d18564 d18475 d18463
      omega
    have d18584 : (x 8 3 && x 8 14).toNat = 0 := by
      have r18585 := hand1 (x 8 3) (x 8 14)
      have b18586 := hb (x 8 3)
      have b18587 := hb (x 8 3 && x 8 14)
      clear * - r18585 b18586 b18587 d18576
      omega
    have d18588 : (x 11 11).toNat = 1 := by
      have r18589 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18590 := hb (x 7 4)
      have b18591 := hb (x 11 11)
      have b18592 := hb (x 10 1 && x 10 12)
      have b18593 := hb (x 9 2 && x 9 13)
      have b18594 := hb (x 8 3 && x 8 14)
      clear * - r18589 b18590 b18591 b18592 b18593 b18594 d18319 d18335 d18584 d18284
      omega
    have d18595 : (x 11 3).toNat = 1 := by
      have r18596 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
      have b18597 := hb (x 11 3)
      have b18598 := hb (x 11 11)
      clear * - r18596 b18597 b18598 d18588
      omega
    have d18599 : (x 14 12).toNat = 0 := by
      have r18600 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18601 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e18602 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b18603 := hb (x 11 3)
      have b18604 := hb (x 12 2)
      have b18605 := hb (x 13 13)
      have b18606 := hb (x 14 12)
      clear * - r18600 e18601 e18602 b18603 b18604 b18605 b18606 d18595
      omega
    have d18607 : (x 14 1 && x 14 12).toNat = 0 := by
      have r18608 := hand2 (x 14 1) (x 14 12)
      have b18609 := hb (x 14 12)
      have b18610 := hb (x 14 1 && x 14 12)
      clear * - r18608 b18609 b18610 d18599
      omega
    have d18611 : (x 14 2 && x 14 12).toNat = 0 := by
      have r18612 := hand2 (x 14 2) (x 14 12)
      have b18613 := hb (x 14 12)
      have b18614 := hb (x 14 2 && x 14 12)
      clear * - r18612 b18613 b18614 d18599
      omega
    have d18615 : (x 13 13).toNat = 0 := by
      have r18616 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18617 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e18618 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b18619 := hb (x 11 3)
      have b18620 := hb (x 12 2)
      have b18621 := hb (x 13 13)
      have b18622 := hb (x 14 12)
      clear * - r18616 e18617 e18618 b18619 b18620 b18621 b18622 d18599 d18595
      omega
    have d18623 : (x 13 2 && x 13 13).toNat = 0 := by
      have r18624 := hand2 (x 13 2) (x 13 13)
      have b18625 := hb (x 13 13)
      have b18626 := hb (x 13 2 && x 13 13)
      clear * - r18624 b18625 b18626 d18615
      omega
    have d18627 : (x 13 3 && x 13 13).toNat = 0 := by
      have r18628 := hand2 (x 13 3) (x 13 13)
      have b18629 := hb (x 13 13)
      have b18630 := hb (x 13 3 && x 13 13)
      clear * - r18628 b18629 b18630 d18615
      omega
    have d18631 : (x 12 1 && x 12 14).toNat = 1 := by
      have r18632 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18633 := hb (x 11 2)
      have b18634 := hb (x 13 13)
      have b18635 := hb (x 12 1 && x 12 14)
      clear * - r18632 b18633 b18634 b18635 d18615 d18443
      omega
    have d18636 : (x 12 1).toNat = 1 := by
      have r18637 := hand1 (x 12 1) (x 12 14)
      have b18638 := hb (x 12 1)
      have b18639 := hb (x 12 1 && x 12 14)
      clear * - r18637 b18638 b18639 d18631
      omega
    have d18640 : (x 13 14).toNat = 0 := by
      have r18641 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18642 := hb (x 12 1)
      have b18643 := hb (x 13 14)
      clear * - r18641 b18642 b18643 d18636
      omega
    have d18644 : (x 13 1 && x 13 14).toNat = 0 := by
      have r18645 := hand2 (x 13 1) (x 13 14)
      have b18646 := hb (x 13 14)
      have b18647 := hb (x 13 1 && x 13 14)
      clear * - r18645 b18646 b18647 d18640
      omega
    have d18648 : (x 13 2).toNat = 0 := by
      have r18649 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
      have b18650 := hb (x 13 2)
      have b18651 := hb (x 13 14)
      clear * - r18649 b18650 b18651 d18640
      omega
    have d18652 : (x 12 2).toNat = 0 := by
      have r18653 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18654 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
      have e18655 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
      have b18656 := hb (x 11 3)
      have b18657 := hb (x 12 2)
      have b18658 := hb (x 13 13)
      have b18659 := hb (x 14 12)
      clear * - r18653 e18654 e18655 b18656 b18657 b18658 b18659 d18599 d18615 d18595
      omega
    have d18660 : (x 14 13).toNat = 1 := by
      have r18661 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18662 := hb (x 12 2)
      have b18663 := hb (x 14 13)
      have b18664 := hb (x 13 1 && x 13 14)
      clear * - r18661 b18662 b18663 b18664 d18644 d18652
      omega
    have d18665 : (x 15 12).toNat = 0 := by
      have r18666 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18667 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e18668 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b18669 := hb (x 12 3)
      have b18670 := hb (x 13 2)
      have b18671 := hb (x 14 13)
      have b18672 := hb (x 15 12)
      clear * - r18666 e18667 e18668 b18669 b18670 b18671 b18672 d18660 d18648
      omega
    have d18673 : (x 12 3).toNat = 0 := by
      have r18674 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18675 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
      have e18676 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
      have b18677 := hb (x 12 3)
      have b18678 := hb (x 13 2)
      have b18679 := hb (x 14 13)
      have b18680 := hb (x 15 12)
      clear * - r18674 e18675 e18676 b18677 b18678 b18679 b18680 d18665 d18660 d18648
      omega
    have d18681 : (x 12 3 && x 12 14).toNat = 0 := by
      have r18682 := hand1 (x 12 3) (x 12 14)
      have b18683 := hb (x 12 3)
      have b18684 := hb (x 12 3 && x 12 14)
      clear * - r18682 b18683 b18684 d18673
      omega
    have d18685 : (x 15 11).toNat = 1 := by
      have r18686 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18687 := hb (x 11 4)
      have b18688 := hb (x 15 11)
      have b18689 := hb (x 14 1 && x 14 12)
      have b18690 := hb (x 13 2 && x 13 13)
      have b18691 := hb (x 12 3 && x 12 14)
      clear * - r18686 b18687 b18688 b18689 b18690 b18691 d18607 d18623 d18681 d18572
      omega
    have d18692 : (x 15 3).toNat = 1 := by
      have r18693 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
      have b18694 := hb (x 15 3)
      have b18695 := hb (x 15 11)
      clear * - r18693 b18694 b18695 d18685
      omega
    have d18696 : (x 18 12).toNat = 0 := by
      have r18697 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18698 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e18699 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b18700 := hb (x 15 3)
      have b18701 := hb (x 16 2)
      have b18702 := hb (x 17 13)
      have b18703 := hb (x 18 12)
      clear * - r18697 e18698 e18699 b18700 b18701 b18702 b18703 d18692
      omega
    have d18704 : (x 17 13).toNat = 0 := by
      have r18705 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18706 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e18707 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b18708 := hb (x 15 3)
      have b18709 := hb (x 16 2)
      have b18710 := hb (x 17 13)
      have b18711 := hb (x 18 12)
      clear * - r18705 e18706 e18707 b18708 b18709 b18710 b18711 d18696 d18692
      omega
    have d18712 : (x 16 1 && x 16 14).toNat = 1 := by
      have r18713 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18714 := hb (x 15 2)
      have b18715 := hb (x 17 13)
      have b18716 := hb (x 16 1 && x 16 14)
      clear * - r18713 b18714 b18715 b18716 d18704 d18556
      omega
    have d18717 : (x 16 14).toNat = 1 := by
      have r18718 := hand2 (x 16 1) (x 16 14)
      have b18719 := hb (x 16 14)
      have b18720 := hb (x 16 1 && x 16 14)
      clear * - r18718 b18719 b18720 d18712
      omega
    have d18721 : (x 15 1).toNat = 0 := by
      have r18722 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b18723 := hb (x 15 1)
      have b18724 := hb (x 16 14)
      clear * - r18722 b18723 b18724 d18717
      omega
    have d18725 : (x 15 1 && x 15 11).toNat = 0 := by
      have r18726 := hand1 (x 15 1) (x 15 11)
      have b18727 := hb (x 15 1)
      have b18728 := hb (x 15 1 && x 15 11)
      clear * - r18726 b18727 b18728 d18721
      omega
    have d18729 : (x 16 2).toNat = 0 := by
      have r18730 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18731 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
      have e18732 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
      have b18733 := hb (x 15 3)
      have b18734 := hb (x 16 2)
      have b18735 := hb (x 17 13)
      have b18736 := hb (x 18 12)
      clear * - r18730 e18731 e18732 b18733 b18734 b18735 b18736 d18696 d18704 d18692
      omega
    have d18737 : (x 16 10).toNat = 0 := by
      have r18738 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
      have b18739 := hb (x 16 2)
      have b18740 := hb (x 16 10)
      clear * - r18738 b18739 b18740 d18729
      omega
    have r18741 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := by have q := hcov10 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b18742 := hb (x 11 5)
    have b18743 := hb (x 16 10)
    have b18744 := hb (x 15 1 && x 15 11)
    have b18745 := hb (x 14 2 && x 14 12)
    have b18746 := hb (x 13 3 && x 13 13)
    have b18747 := hb (x 12 4 && x 12 14)
    linarith only [r18741, b18742, b18743, b18744, b18745, b18746, b18747, d18737, d18725, d18611, d18627, d18509, d18521]
  · have f18748 : (x (-1) 4).toNat = 1 := by rw [h18181]; rfl
    have d18749 : (x 3 8).toNat = 0 := by
      have r18750 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18751 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e18752 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e18753 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e18754 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e18755 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e18756 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b18757 := hb (x (-4) 7)
      have b18758 := hb (x (-3) 6)
      have b18759 := hb (x (-2) 5)
      have b18760 := hb (x (-1) 4)
      have b18761 := hb (x 0 11)
      have b18762 := hb (x 1 10)
      have b18763 := hb (x 2 9)
      have b18764 := hb (x 3 8)
      clear * - r18750 e18751 e18752 e18753 e18754 e18755 e18756 b18757 b18758 b18759 b18760 b18761 b18762 b18763 b18764 g8 g5 f18748 g0
      omega
    have d18765 : (x 2 9).toNat = 0 := by
      have r18766 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e18767 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
      have e18768 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
      have e18769 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
      have e18770 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
      have e18771 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
      have e18772 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
      have b18773 := hb (x (-4) 7)
      have b18774 := hb (x (-3) 6)
      have b18775 := hb (x (-2) 5)
      have b18776 := hb (x (-1) 4)
      have b18777 := hb (x 0 11)
      have b18778 := hb (x 1 10)
      have b18779 := hb (x 2 9)
      have b18780 := hb (x 3 8)
      clear * - r18766 e18767 e18768 e18769 e18770 e18771 e18772 b18773 b18774 b18775 b18776 b18777 b18778 b18779 b18780 d18749 g8 g5 f18748 g0
      omega
    have d18781 : (x 2 9 && x 2 13).toNat = 0 := by
      have r18782 := hand1 (x 2 9) (x 2 13)
      have b18783 := hb (x 2 9)
      have b18784 := hb (x 2 9 && x 2 13)
      clear * - r18782 b18783 b18784 d18765
      omega
    have r18785 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r18786 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r18787 : (x 18 1).toNat + (x 17 2).toNat + (x 16 3).toNat + (x 15 4).toNat + (x 14 5).toNat + (x 13 6).toNat + (x 12 7).toNat + (x 11 8).toNat + (x 10 9).toNat + (x 9 10).toNat + (x 8 11).toNat + (x 7 12).toNat + (x 6 13).toNat + (x 5 14).toNat = 3 := by have q := hcount 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r18788 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18789 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
    have e18790 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
    have e18791 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
    have e18792 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
    have e18793 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
    have e18794 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
    have r18795 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18796 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
    have e18797 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
    have e18798 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
    have e18799 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
    have e18800 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
    have e18801 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
    have r18802 : (x 11 8).toNat + (x 10 1 && x 10 9).toNat + (x 9 2 && x 9 10).toNat + (x 8 3 && x 8 11).toNat + (x 7 4 && x 7 12).toNat + (x 6 5 && x 6 13).toNat + (x 5 6 && x 5 14).toNat + (x 4 7).toNat = 1 := by have q := hd8 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18803 : (x 10 1 && x 10 9).toNat = (x 10 9).toNat := handr _ _ (fun h => hp9 10 (h))
    have e18804 : (x 9 2 && x 9 10).toNat = (x 9 10).toNat := handr _ _ (fun h => hp10 9 (h))
    have e18805 : (x 8 3 && x 8 11).toNat = (x 8 11).toNat := handr _ _ (fun h => hp11 8 (h))
    have e18806 : (x 7 4 && x 7 12).toNat = (x 7 4).toNat := handl _ _ (fun h => hp4 7 (h))
    have e18807 : (x 6 5 && x 6 13).toNat = (x 6 5).toNat := handl _ _ (fun h => hp5 6 (h))
    have e18808 : (x 5 6 && x 5 14).toNat = (x 5 6).toNat := handl _ _ (fun h => hp6 5 (h))
    have r18809 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18810 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
    have e18811 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
    have e18812 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
    have e18813 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
    have e18814 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
    have e18815 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
    have r18816 : (x 19 8).toNat + (x 18 1 && x 18 9).toNat + (x 17 2 && x 17 10).toNat + (x 16 3 && x 16 11).toNat + (x 15 4 && x 15 12).toNat + (x 14 5 && x 14 13).toNat + (x 13 6 && x 13 14).toNat + (x 12 7).toNat = 1 := by have q := hd8 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18817 : (x 18 1 && x 18 9).toNat = (x 18 9).toNat := handr _ _ (fun h => hp9 18 (h))
    have e18818 : (x 17 2 && x 17 10).toNat = (x 17 10).toNat := handr _ _ (fun h => hp10 17 (h))
    have e18819 : (x 16 3 && x 16 11).toNat = (x 16 11).toNat := handr _ _ (fun h => hp11 16 (h))
    have e18820 : (x 15 4 && x 15 12).toNat = (x 15 4).toNat := handl _ _ (fun h => hp4 15 (h))
    have e18821 : (x 14 5 && x 14 13).toNat = (x 14 5).toNat := handl _ _ (fun h => hp5 14 (h))
    have e18822 : (x 13 6 && x 13 14).toNat = (x 13 6).toNat := handl _ _ (fun h => hp6 13 (h))
    have r18823 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18824 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e18825 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have r18826 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18827 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
    have e18828 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
    have r18829 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18830 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
    have e18831 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
    have r18832 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18833 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
    have e18834 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
    have r18835 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18836 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
    have e18837 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
    have r18838 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r18839 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r18840 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r18841 : 1 ≤ (x 14 1).toNat + (x 13 1 && x 13 2).toNat + (x 12 2 && x 12 3).toNat + (x 11 3 && x 11 4).toNat + (x 10 4 && x 10 5).toNat + (x 9 5 && x 9 6).toNat + (x 8 6 && x 8 7).toNat + (x 7 7 && x 7 8).toNat + (x 6 8 && x 6 9).toNat + (x 5 9 && x 5 10).toNat + (x 4 10 && x 4 11).toNat + (x 3 11 && x 3 12).toNat + (x 2 12 && x 2 13).toNat + (x 1 13 && x 1 14).toNat + (x 0 14).toNat := by have q := hcov1 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r18842 : 1 ≤ (x 11 4).toNat + (x 10 1 && x 10 5).toNat + (x 9 2 && x 9 6).toNat + (x 8 3 && x 8 7).toNat + (x 7 4 && x 7 8).toNat + (x 6 5 && x 6 9).toNat + (x 5 6 && x 5 10).toNat + (x 4 7 && x 4 11).toNat + (x 3 8 && x 3 12).toNat + (x 2 9 && x 2 13).toNat + (x 1 10 && x 1 14).toNat + (x 0 11).toNat := by have q := hcov4 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e18843 : (x 10 1 && x 10 5).toNat = (x 10 5).toNat := handr _ _ (fun h => hp13 10 (hp5 10 (h)))
    have e18844 : (x 1 10 && x 1 14).toNat = (x 1 10).toNat := handl _ _ (fun h => hp2 1 (hp10 1 (h)))
    have r18845 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r18846 : 1 ≤ (x 4 10).toNat + (x 3 1 && x 3 11).toNat + (x 2 2 && x 2 12).toNat + (x 1 3 && x 1 13).toNat + (x 0 4 && x 0 14).toNat + (x (-1) 5).toNat := by have q := hcov10 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r18847 : 1 ≤ (x 9 10).toNat + (x 8 1 && x 8 11).toNat + (x 7 2 && x 7 12).toNat + (x 6 3 && x 6 13).toNat + (x 5 4 && x 5 14).toNat + (x 4 5).toNat := by have q := hcov10 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r18848 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r18849 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r18850 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r18851 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := by have q := hcov13 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have r18852 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
    have r18853 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
    have r18854 : (x 4 11).toNat ≤ (x 4 3).toNat := himp _ _ (hp11 4)
    have r18855 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
    have r18856 : (x 16 2).toNat ≤ (x 16 14).toNat := himp _ _ (hp2 16)
    have r18857 := hand2 (x 13 1) (x 13 2)
    have r18858 := hand2 (x 12 2) (x 12 3)
    have r18859 := hand2 (x 11 3) (x 11 4)
    have r18860 := hand2 (x 10 4) (x 10 5)
    have r18861 := hand2 (x 9 5) (x 9 6)
    have r18862 := hand2 (x 8 6) (x 8 7)
    have r18863 := hand2 (x 7 7) (x 7 8)
    have r18864 := hand1 (x 6 8) (x 6 9)
    have r18865 := hand1 (x 5 9) (x 5 10)
    have r18866 := hand2 (x 4 10) (x 4 11)
    have r18867 := hand2 (x 9 2) (x 9 6)
    have r18868 := hand2 (x 8 3) (x 8 7)
    have r18869 := hand2 (x 7 4) (x 7 8)
    have r18870 := hand1 (x 6 5) (x 6 9)
    have r18871 := hand1 (x 5 6) (x 5 10)
    have r18872 := hand1 (x 4 7) (x 4 11)
    have r18873 := hand2 (x 5 1) (x 5 10)
    have r18874 := hand2 (x 4 2) (x 4 11)
    have r18875 := hand2 (x 3 1) (x 3 11)
    have r18876 := hand2 (x 8 1) (x 8 11)
    have r18877 := hand2 (x 7 2) (x 7 12)
    have r18878 := hand2 (x 6 3) (x 6 13)
    have r18879 := hand1 (x 5 4) (x 5 14)
    have r18880 := hand2 (x 14 1) (x 14 11)
    have r18881 := hand1 (x 13 2) (x 13 12)
    have r18882 := hand1 (x 12 3) (x 12 13)
    have r18883 := hand1 (x 11 4) (x 11 14)
    have r18884 := hand1 (x 4 1) (x 4 14)
    have r18885 := hand1 (x 14 1) (x 14 14)
    have r18886 := hand2 (x 17 1) (x 17 14)
    have b18970 := hb (x 18 1)
    linarith only [r18785, r18786, r18787, r18788, e18789, e18790, e18791, e18792, e18793, e18794, r18795, e18796, e18797, e18798, e18799, e18800, e18801, r18802, e18803, e18804, e18805, e18806, e18807, e18808, r18809, e18810, e18811, e18812, e18813, e18814, e18815, r18816, e18817, e18818, e18819, e18820, e18821, e18822, r18823, e18824, e18825, r18826, e18827, e18828, r18829, e18830, e18831, r18832, e18833, e18834, r18835, e18836, e18837, r18838, r18839, r18840, r18841, r18842, e18843, e18844, r18845, r18846, r18847, r18848, r18849, r18850, r18851, r18852, r18853, r18854, r18855, r18856, r18857, r18858, r18859, r18860, r18861, r18862, r18863, r18864, r18865, r18866, r18867, r18868, r18869, r18870, r18871, r18872, r18873, r18874, r18875, r18876, r18877, r18878, r18879, r18880, r18881, r18882, r18883, r18884, r18885, r18886, b18970, g2, g4, g5, g6, g7, g8, g10, d18173, g11, g12, g14, g15, g16, g17, d18169, g18, g19, d18781, g20, d18177, g21, d18165, g22, g23]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt0000011 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x (-4) 11).toNat = 0)
    (g1 : (x (-3) 10).toNat = 0)
    (g2 : (x (-2) 5).toNat = 0)
    (g3 : (x (-2) 9).toNat = 0)
    (g4 : (x (-2) 10).toNat = 0)
    (g5 : (x (-1) 5).toNat = 1)
    (g6 : (x 0 2).toNat = 0)
    (g7 : (x 0 3).toNat = 0)
    (g8 : (x 0 4).toNat = 0)
    (g9 : (x 0 5).toNat = 0)
    (g10 : (x 0 6).toNat = 0)
    (g11 : (x 0 7).toNat = 0)
    (g12 : (x 0 10).toNat = 0)
    (g13 : (x 0 11).toNat = 0)
    (g14 : (x 0 12).toNat = 0)
    (g15 : (x 0 13).toNat = 0)
    (g16 : (x 0 14).toNat = 0)
    (g17 : (x 1 2).toNat = 0)
    (g18 : (x 1 4).toNat = 0)
    (g19 : (x 1 5).toNat = 0)
    (g20 : (x 1 9).toNat = 0)
    (g21 : (x 1 10).toNat = 0)
    (g22 : (x 1 13).toNat = 0)
    (g23 : (x 1 14).toNat = 1)
    (g24 : (x 2 1).toNat = 1)
    (g25 : (x 2 13).toNat = 1)
    (g26 : (x 3 2).toNat = 0)
    (g27 : (x 3 4).toNat = 0)
    (g28 : (x 3 10).toNat = 0)
    (g29 : (x 3 12).toNat = 0)
    (g30 : (x 3 11 && x 3 12).toNat = 0)
    (g31 : (x 1 13 && x 1 14).toNat = 0)
    (g32 : (x 3 10 && x 3 12).toNat = 0)
    (g33 : (x 1 12 && x 1 14).toNat = 0)
    (g34 : (x 3 9 && x 3 12).toNat = 0)
    (g35 : (x 0 2 && x 0 6).toNat = 0)
    (g36 : (x 1 2 && x 1 6).toNat = 0)
    (g37 : (x 0 3 && x 0 7).toNat = 0)
    (g38 : (x (-2) 5 && x (-2) 9).toNat = 0)
    (g39 : (x (-3) 6 && x (-3) 10).toNat = 0)
    (g40 : (x (-4) 7 && x (-4) 11).toNat = 0)
    (g41 : (x 1 5 && x 1 9).toNat = 0)
    (g42 : (x 0 6 && x 0 10).toNat = 0)
    (g43 : (x 3 7 && x 3 12).toNat = 0)
    (g44 : (x 1 9 && x 1 14).toNat = 0)
    (g45 : (x (-3) 1 && x (-3) 10).toNat = 0)
    (g46 : (x (-4) 2 && x (-4) 11).toNat = 0)
    (g47 : (x 1 2 && x 1 11).toNat = 0)
    (g48 : (x 0 3 && x 0 12).toNat = 0)
    (g49 : (x (-2) 5 && x (-2) 14).toNat = 0)
    (g50 : (x 3 2 && x 3 11).toNat = 0)
    (g51 : (x 1 4 && x 1 13).toNat = 0)
    (g52 : (x 0 5 && x 0 14).toNat = 0)
    (g53 : (x 3 3 && x 3 12).toNat = 0)
    (g54 : (x 1 5 && x 1 14).toNat = 0)
    (g55 : (x (-3) 1 && x (-3) 11).toNat = 0)
    (g56 : (x 1 1 && x 1 11).toNat = 0)
    (g57 : (x 0 2 && x 0 12).toNat = 0)
    (g58 : (x 3 2 && x 3 12).toNat = 0)
    (g59 : (x 1 4 && x 1 14).toNat = 0)
    (g60 : (x (-2) 1 && x (-2) 12).toNat = 0)
    (g61 : (x (-3) 2 && x (-3) 13).toNat = 0)
    (g62 : (x (-4) 3 && x (-4) 14).toNat = 0)
    (g63 : (x 1 2 && x 1 13).toNat = 0)
    (g64 : (x 0 3 && x 0 14).toNat = 0)
    (g65 : (x 3 1 && x 3 12).toNat = 0)
    (g66 : (x 3 2 && x 3 13).toNat = 0)
    (g67 : (x 3 3 && x 3 14).toNat = 0)
    (g68 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d19017 : (x 4 8).toNat = 0 := by
    have r19018 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19019 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e19020 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e19021 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e19022 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e19023 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e19024 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b19025 := hb (x (-3) 7)
    have b19026 := hb (x (-2) 6)
    have b19027 := hb (x (-1) 5)
    have b19028 := hb (x 0 4)
    have b19029 := hb (x 1 11)
    have b19030 := hb (x 2 10)
    have b19031 := hb (x 3 9)
    have b19032 := hb (x 4 8)
    clear * - r19018 e19019 e19020 e19021 e19022 e19023 e19024 b19025 b19026 b19027 b19028 b19029 b19030 b19031 b19032 g8 g5
    omega
  have d19033 : (x 4 8 && x 4 11).toNat = 0 := by
    have r19034 := hand1 (x 4 8) (x 4 11)
    have b19035 := hb (x 4 8)
    have b19036 := hb (x 4 8 && x 4 11)
    clear * - r19034 b19035 b19036 d19017
    omega
  have d19037 : (x 3 9).toNat = 0 := by
    have r19038 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19039 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e19040 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e19041 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e19042 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e19043 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e19044 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b19045 := hb (x (-3) 7)
    have b19046 := hb (x (-2) 6)
    have b19047 := hb (x (-1) 5)
    have b19048 := hb (x 0 4)
    have b19049 := hb (x 1 11)
    have b19050 := hb (x 2 10)
    have b19051 := hb (x 3 9)
    have b19052 := hb (x 4 8)
    clear * - r19038 e19039 e19040 e19041 e19042 e19043 e19044 b19045 b19046 b19047 b19048 b19049 b19050 b19051 b19052 d19017 g8 g5
    omega
  have d19053 : (x 2 10).toNat = 0 := by
    have r19054 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19055 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e19056 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e19057 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e19058 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e19059 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e19060 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b19061 := hb (x (-3) 7)
    have b19062 := hb (x (-2) 6)
    have b19063 := hb (x (-1) 5)
    have b19064 := hb (x 0 4)
    have b19065 := hb (x 1 11)
    have b19066 := hb (x 2 10)
    have b19067 := hb (x 3 9)
    have b19068 := hb (x 4 8)
    clear * - r19054 e19055 e19056 e19057 e19058 e19059 e19060 b19061 b19062 b19063 b19064 b19065 b19066 b19067 b19068 d19017 d19037 g8 g5
    omega
  have d19069 : (x 2 1 && x 2 10).toNat = 0 := by
    have r19070 := hand2 (x 2 1) (x 2 10)
    have b19071 := hb (x 2 10)
    have b19072 := hb (x 2 1 && x 2 10)
    clear * - r19070 b19071 b19072 d19053
    omega
  have d19073 : (x 2 10 && x 2 13).toNat = 0 := by
    have r19074 := hand1 (x 2 10) (x 2 13)
    have b19075 := hb (x 2 10)
    have b19076 := hb (x 2 10 && x 2 13)
    clear * - r19074 b19075 b19076 d19053
    omega
  have d19077 : (x 1 11).toNat = 0 := by
    have r19078 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19079 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e19080 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e19081 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e19082 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e19083 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e19084 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b19085 := hb (x (-3) 7)
    have b19086 := hb (x (-2) 6)
    have b19087 := hb (x (-1) 5)
    have b19088 := hb (x 0 4)
    have b19089 := hb (x 1 11)
    have b19090 := hb (x 2 10)
    have b19091 := hb (x 3 9)
    have b19092 := hb (x 4 8)
    clear * - r19078 e19079 e19080 e19081 e19082 e19083 e19084 b19085 b19086 b19087 b19088 b19089 b19090 b19091 b19092 d19017 d19037 d19053 g8 g5
    omega
  have d19093 : (x 1 11 && x 1 14).toNat = 0 := by
    have r19094 := hand1 (x 1 11) (x 1 14)
    have b19095 := hb (x 1 11)
    have b19096 := hb (x 1 11 && x 1 14)
    clear * - r19094 b19095 b19096 d19077
    omega
  have d19097 : (x (-2) 6).toNat = 0 := by
    have r19098 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19099 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e19100 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e19101 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e19102 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e19103 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e19104 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b19105 := hb (x (-3) 7)
    have b19106 := hb (x (-2) 6)
    have b19107 := hb (x (-1) 5)
    have b19108 := hb (x 0 4)
    have b19109 := hb (x 1 11)
    have b19110 := hb (x 2 10)
    have b19111 := hb (x 3 9)
    have b19112 := hb (x 4 8)
    clear * - r19098 e19099 e19100 e19101 e19102 e19103 e19104 b19105 b19106 b19107 b19108 b19109 b19110 b19111 b19112 d19017 d19037 d19053 d19077 g8 g5
    omega
  have d19113 : (x (-3) 7).toNat = 0 := by
    have r19114 : (x 4 8).toNat + (x 3 1 && x 3 9).toNat + (x 2 2 && x 2 10).toNat + (x 1 3 && x 1 11).toNat + (x 0 4 && x 0 12).toNat + (x (-1) 5 && x (-1) 13).toNat + (x (-2) 6 && x (-2) 14).toNat + (x (-3) 7).toNat = 1 := by have q := hd8 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e19115 : (x 3 1 && x 3 9).toNat = (x 3 9).toNat := handr _ _ (fun h => hp9 3 (h))
    have e19116 : (x 2 2 && x 2 10).toNat = (x 2 10).toNat := handr _ _ (fun h => hp10 2 (h))
    have e19117 : (x 1 3 && x 1 11).toNat = (x 1 11).toNat := handr _ _ (fun h => hp11 1 (h))
    have e19118 : (x 0 4 && x 0 12).toNat = (x 0 4).toNat := handl _ _ (fun h => hp4 0 (h))
    have e19119 : (x (-1) 5 && x (-1) 13).toNat = (x (-1) 5).toNat := handl _ _ (fun h => hp5 (-1) (h))
    have e19120 : (x (-2) 6 && x (-2) 14).toNat = (x (-2) 6).toNat := handl _ _ (fun h => hp6 (-2) (h))
    have b19121 := hb (x (-3) 7)
    have b19122 := hb (x (-2) 6)
    have b19123 := hb (x (-1) 5)
    have b19124 := hb (x 0 4)
    have b19125 := hb (x 1 11)
    have b19126 := hb (x 2 10)
    have b19127 := hb (x 3 9)
    have b19128 := hb (x 4 8)
    clear * - r19114 e19115 e19116 e19117 e19118 e19119 e19120 b19121 b19122 b19123 b19124 b19125 b19126 b19127 b19128 d19017 d19037 d19053 d19077 g8 g5 d19097
    omega
  cases h19129 : x (-1) 11
  · have f19130 : (x (-1) 11).toNat = 0 := by rw [h19129]; rfl
    have d19131 : (x (-1) 7 && x (-1) 11).toNat = 0 := by
      have r19132 := hand2 (x (-1) 7) (x (-1) 11)
      have b19133 := hb (x (-1) 11)
      have b19134 := hb (x (-1) 7 && x (-1) 11)
      clear * - r19132 b19133 b19134 f19130
      omega
    have d19135 : (x (-5) 4).toNat = 1 := by
      have r19136 : 1 ≤ (x (-1) 11).toNat + (x (-2) 1 && x (-2) 12).toNat + (x (-3) 2 && x (-3) 13).toNat + (x (-4) 3 && x (-4) 14).toNat + (x (-5) 4).toNat := by have q := hcov11 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b19137 := hb (x (-5) 4)
      have b19138 := hb (x (-1) 11)
      have b19139 := hb (x (-2) 1 && x (-2) 12)
      have b19140 := hb (x (-3) 2 && x (-3) 13)
      have b19141 := hb (x (-4) 3 && x (-4) 14)
      clear * - r19136 b19137 b19138 b19139 b19140 b19141 f19130 g60 g61 g62
      omega
    have d19142 : (x (-5) 12).toNat = 1 := by
      have r19143 : (x (-5) 4).toNat ≤ (x (-5) 12).toNat := himp _ _ (hp4 (-5))
      have b19144 := hb (x (-5) 4)
      have b19145 := hb (x (-5) 12)
      clear * - r19143 b19144 b19145 d19135
      omega
    have d19146 : (x (-6) 13).toNat = 0 := by
      have r19147 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19148 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e19149 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b19150 := hb (x (-8) 3)
      have b19151 := hb (x (-7) 2)
      have b19152 := hb (x (-6) 13)
      have b19153 := hb (x (-5) 12)
      clear * - r19147 e19148 e19149 b19150 b19151 b19152 b19153 d19142
      omega
    have d19154 : (x (-6) 4 && x (-6) 13).toNat = 0 := by
      have r19155 := hand2 (x (-6) 4) (x (-6) 13)
      have b19156 := hb (x (-6) 13)
      have b19157 := hb (x (-6) 4 && x (-6) 13)
      clear * - r19155 b19156 b19157 d19146
      omega
    have d19158 : (x (-6) 9 && x (-6) 13).toNat = 0 := by
      have r19159 := hand2 (x (-6) 9) (x (-6) 13)
      have b19160 := hb (x (-6) 13)
      have b19161 := hb (x (-6) 9 && x (-6) 13)
      clear * - r19159 b19160 b19161 d19146
      omega
    have d19162 : (x (-6) 5).toNat = 0 := by
      have r19163 : (x (-6) 5).toNat ≤ (x (-6) 13).toNat := himp _ _ (hp5 (-6))
      have b19164 := hb (x (-6) 5)
      have b19165 := hb (x (-6) 13)
      clear * - r19163 b19164 b19165 d19146
      omega
    have d19166 : (x (-7) 2).toNat = 0 := by
      have r19167 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19168 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e19169 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b19170 := hb (x (-8) 3)
      have b19171 := hb (x (-7) 2)
      have b19172 := hb (x (-6) 13)
      have b19173 := hb (x (-5) 12)
      clear * - r19167 e19168 e19169 b19170 b19171 b19172 b19173 d19142 d19146
      omega
    have d19174 : (x (-7) 2 && x (-7) 13).toNat = 0 := by
      have r19175 := hand1 (x (-7) 2) (x (-7) 13)
      have b19176 := hb (x (-7) 2)
      have b19177 := hb (x (-7) 2 && x (-7) 13)
      clear * - r19175 b19176 b19177 d19166
      omega
    have d19178 : (x (-7) 2 && x (-7) 11).toNat = 0 := by
      have r19179 := hand1 (x (-7) 2) (x (-7) 11)
      have b19180 := hb (x (-7) 2)
      have b19181 := hb (x (-7) 2 && x (-7) 11)
      clear * - r19179 b19180 b19181 d19166
      omega
    have d19182 : (x (-7) 10).toNat = 0 := by
      have r19183 : (x (-7) 10).toNat ≤ (x (-7) 2).toNat := himp _ _ (hp10 (-7))
      have b19184 := hb (x (-7) 2)
      have b19185 := hb (x (-7) 10)
      clear * - r19183 b19184 b19185 d19166
      omega
    have d19186 : (x (-8) 3).toNat = 0 := by
      have r19187 : (x (-5) 12).toNat + (x (-6) 1 && x (-6) 13).toNat + (x (-7) 2 && x (-7) 14).toNat + (x (-8) 3).toNat = 1 := by have q := hd12 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19188 : (x (-6) 1 && x (-6) 13).toNat = (x (-6) 13).toNat := handr _ _ (fun h => hp13 (-6) (h))
      have e19189 : (x (-7) 2 && x (-7) 14).toNat = (x (-7) 2).toNat := handl _ _ (fun h => hp2 (-7) (h))
      have b19190 := hb (x (-8) 3)
      have b19191 := hb (x (-7) 2)
      have b19192 := hb (x (-6) 13)
      have b19193 := hb (x (-5) 12)
      clear * - r19187 e19188 e19189 b19190 b19191 b19192 b19193 d19142 d19146 d19166
      omega
    have d19194 : (x (-8) 3 && x (-8) 14).toNat = 0 := by
      have r19195 := hand1 (x (-8) 3) (x (-8) 14)
      have b19196 := hb (x (-8) 3)
      have b19197 := hb (x (-8) 3 && x (-8) 14)
      clear * - r19195 b19196 b19197 d19186
      omega
    have d19198 : (x (-8) 3 && x (-8) 12).toNat = 0 := by
      have r19199 := hand1 (x (-8) 3) (x (-8) 12)
      have b19200 := hb (x (-8) 3)
      have b19201 := hb (x (-8) 3 && x (-8) 12)
      clear * - r19199 b19200 b19201 d19186
      omega
    have d19202 : (x (-8) 11).toNat = 0 := by
      have r19203 : (x (-8) 11).toNat ≤ (x (-8) 3).toNat := himp _ _ (hp11 (-8))
      have b19204 := hb (x (-8) 3)
      have b19205 := hb (x (-8) 11)
      clear * - r19203 b19204 b19205 d19186
      omega
    have d19206 : (x (-1) 8).toNat = 0 := by
      have r19207 : (x (-1) 8).toNat + (x (-2) 1 && x (-2) 9).toNat + (x (-3) 2 && x (-3) 10).toNat + (x (-4) 3 && x (-4) 11).toNat + (x (-5) 4 && x (-5) 12).toNat + (x (-6) 5 && x (-6) 13).toNat + (x (-7) 6 && x (-7) 14).toNat + (x (-8) 7).toNat = 1 := by have q := hd8 (-1); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19208 : (x (-2) 1 && x (-2) 9).toNat = (x (-2) 9).toNat := handr _ _ (fun h => hp9 (-2) (h))
      have e19209 : (x (-3) 2 && x (-3) 10).toNat = (x (-3) 10).toNat := handr _ _ (fun h => hp10 (-3) (h))
      have e19210 : (x (-4) 3 && x (-4) 11).toNat = (x (-4) 11).toNat := handr _ _ (fun h => hp11 (-4) (h))
      have e19211 : (x (-5) 4 && x (-5) 12).toNat = (x (-5) 4).toNat := handl _ _ (fun h => hp4 (-5) (h))
      have e19212 : (x (-6) 5 && x (-6) 13).toNat = (x (-6) 5).toNat := handl _ _ (fun h => hp5 (-6) (h))
      have e19213 : (x (-7) 6 && x (-7) 14).toNat = (x (-7) 6).toNat := handl _ _ (fun h => hp6 (-7) (h))
      have b19214 := hb (x (-8) 7)
      have b19215 := hb (x (-7) 6)
      have b19216 := hb (x (-6) 5)
      have b19217 := hb (x (-5) 4)
      have b19218 := hb (x (-4) 11)
      have b19219 := hb (x (-3) 10)
      have b19220 := hb (x (-2) 9)
      have b19221 := hb (x (-1) 8)
      clear * - r19207 e19208 e19209 e19210 e19211 e19212 e19213 b19214 b19215 b19216 b19217 b19218 b19219 b19220 b19221 g3 g1 g0 d19135 d19162
      omega
    have d19222 : (x (-1) 4 && x (-1) 8).toNat = 0 := by
      have r19223 := hand2 (x (-1) 4) (x (-1) 8)
      have b19224 := hb (x (-1) 8)
      have b19225 := hb (x (-1) 4 && x (-1) 8)
      clear * - r19223 b19224 b19225 d19206
      omega
    cases h19226 : x (-1) 3
    · have f19227 : (x (-1) 3).toNat = 0 := by rw [h19226]; rfl
      have d19228 : (x (-1) 3 && x (-1) 13).toNat = 0 := by
        have r19229 := hand1 (x (-1) 3) (x (-1) 13)
        have b19230 := hb (x (-1) 3)
        have b19231 := hb (x (-1) 3 && x (-1) 13)
        clear * - r19229 b19230 b19231 f19227
        omega
      have r19232 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19233 : (x 6 1).toNat + (x 5 2).toNat + (x 4 3).toNat + (x 3 4).toNat + (x 2 5).toNat + (x 1 6).toNat + (x 0 7).toNat + (x (-1) 8).toNat + (x (-2) 9).toNat + (x (-3) 10).toNat + (x (-4) 11).toNat + (x (-5) 12).toNat + (x (-6) 13).toNat + (x (-7) 14).toNat = 3 := by have q := hcount 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19234 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19235 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
      have e19236 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
      have e19237 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
      have e19238 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
      have e19239 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
      have e19240 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
      have r19241 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19242 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e19243 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e19244 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e19245 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e19246 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e19247 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have r19248 : (x 10 8).toNat + (x 9 1 && x 9 9).toNat + (x 8 2 && x 8 10).toNat + (x 7 3 && x 7 11).toNat + (x 6 4 && x 6 12).toNat + (x 5 5 && x 5 13).toNat + (x 4 6 && x 4 14).toNat + (x 3 7).toNat = 1 := by have q := hd8 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19249 : (x 9 1 && x 9 9).toNat = (x 9 9).toNat := handr _ _ (fun h => hp9 9 (h))
      have e19250 : (x 8 2 && x 8 10).toNat = (x 8 10).toNat := handr _ _ (fun h => hp10 8 (h))
      have e19251 : (x 7 3 && x 7 11).toNat = (x 7 11).toNat := handr _ _ (fun h => hp11 7 (h))
      have e19252 : (x 6 4 && x 6 12).toNat = (x 6 4).toNat := handl _ _ (fun h => hp4 6 (h))
      have e19253 : (x 5 5 && x 5 13).toNat = (x 5 5).toNat := handl _ _ (fun h => hp5 5 (h))
      have e19254 : (x 4 6 && x 4 14).toNat = (x 4 6).toNat := handl _ _ (fun h => hp6 4 (h))
      have r19255 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19256 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
      have e19257 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
      have r19258 : (x (-2) 12).toNat + (x (-3) 1 && x (-3) 13).toNat + (x (-4) 2 && x (-4) 14).toNat + (x (-5) 3).toNat = 1 := by have q := hd12 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19259 : (x (-3) 1 && x (-3) 13).toNat = (x (-3) 13).toNat := handr _ _ (fun h => hp13 (-3) (h))
      have e19260 : (x (-4) 2 && x (-4) 14).toNat = (x (-4) 2).toNat := handl _ _ (fun h => hp2 (-4) (h))
      have r19261 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19262 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
      have e19263 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
      have r19264 : 1 ≤ (x 6 4).toNat + (x 5 1 && x 5 5).toNat + (x 4 2 && x 4 6).toNat + (x 3 3 && x 3 7).toNat + (x 2 4 && x 2 8).toNat + (x 1 5 && x 1 9).toNat + (x 0 6 && x 0 10).toNat + (x (-1) 7 && x (-1) 11).toNat + (x (-2) 8 && x (-2) 12).toNat + (x (-3) 9 && x (-3) 13).toNat + (x (-4) 10 && x (-4) 14).toNat + (x (-5) 11).toNat := by have q := hcov4 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19265 : (x 5 1 && x 5 5).toNat = (x 5 5).toNat := handr _ _ (fun h => hp13 5 (hp5 5 (h)))
      have e19266 : (x (-4) 10 && x (-4) 14).toNat = (x (-4) 10).toNat := handl _ _ (fun h => hp2 (-4) (hp10 (-4) (h)))
      have r19267 : 1 ≤ (x (-2) 9).toNat + (x (-3) 1 && x (-3) 10).toNat + (x (-4) 2 && x (-4) 11).toNat + (x (-5) 3 && x (-5) 12).toNat + (x (-6) 4 && x (-6) 13).toNat + (x (-7) 5 && x (-7) 14).toNat + (x (-8) 6).toNat := by have q := hcov9 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19268 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19269 : 1 ≤ (x (-2) 10).toNat + (x (-3) 1 && x (-3) 11).toNat + (x (-4) 2 && x (-4) 12).toNat + (x (-5) 3 && x (-5) 13).toNat + (x (-6) 4 && x (-6) 14).toNat + (x (-7) 5).toNat := by have q := hcov10 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19270 : 1 ≤ (x 2 10).toNat + (x 1 1 && x 1 11).toNat + (x 0 2 && x 0 12).toNat + (x (-1) 3 && x (-1) 13).toNat + (x (-2) 4 && x (-2) 14).toNat + (x (-3) 5).toNat := by have q := hcov10 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19271 : 1 ≤ (x (-5) 11).toNat + (x (-6) 1 && x (-6) 12).toNat + (x (-7) 2 && x (-7) 13).toNat + (x (-8) 3 && x (-8) 14).toNat + (x (-9) 4).toNat := by have q := hcov11 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19272 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19273 : 1 ≤ (x (-6) 13).toNat + (x (-7) 1 && x (-7) 14).toNat + (x (-8) 2).toNat := by have q := hcov13 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19274 : (x (-9) 4).toNat ≤ (x (-9) 12).toNat := himp _ _ (hp4 (-9))
      have r19275 : (x (-7) 5).toNat ≤ (x (-7) 13).toNat := himp _ _ (hp5 (-7))
      have r19276 : (x (-3) 5).toNat ≤ (x (-3) 13).toNat := himp _ _ (hp5 (-3))
      have r19277 : (x (-2) 4).toNat ≤ (x (-2) 12).toNat := himp _ _ (hp4 (-2))
      have r19278 := hand1 (x (-5) 8) (x (-5) 12)
      have r19279 := hand2 (x 4 2) (x 4 6)
      have r19280 := hand2 (x 3 3) (x 3 7)
      have r19281 := hand2 (x 2 4) (x 2 8)
      have r19282 := hand1 (x (-2) 8) (x (-2) 12)
      have r19283 := hand1 (x (-3) 9) (x (-3) 13)
      have r19284 := hand1 (x (-5) 3) (x (-5) 12)
      have r19285 := hand1 (x (-7) 5) (x (-7) 14)
      have r19286 := hand1 (x (-1) 4) (x (-1) 13)
      have r19287 := hand1 (x (-4) 2) (x (-4) 12)
      have r19288 := hand1 (x (-5) 3) (x (-5) 13)
      have r19289 := hand1 (x (-6) 4) (x (-6) 14)
      have r19290 := hand1 (x (-2) 4) (x (-2) 14)
      have r19291 := hand2 (x (-6) 1) (x (-6) 12)
      have r19292 := hand1 (x 6 1) (x 6 12)
      have r19293 := hand1 (x 5 2) (x 5 13)
      have r19294 := hand1 (x 4 3) (x 4 14)
      have r19295 := hand2 (x (-7) 1) (x (-7) 14)
      linarith only [r19232, r19233, r19234, e19235, e19236, e19237, e19238, e19239, e19240, r19241, e19242, e19243, e19244, e19245, e19246, e19247, r19248, e19249, e19250, e19251, e19252, e19253, e19254, r19255, e19256, e19257, r19258, e19259, e19260, r19261, e19262, e19263, r19264, e19265, e19266, r19267, r19268, r19269, r19270, r19271, r19272, r19273, r19274, r19275, r19276, r19277, r19278, r19279, r19280, r19281, r19282, r19283, r19284, r19285, r19286, r19287, r19288, r19289, r19290, r19291, r19292, r19293, r19294, r19295, d19202, d19182, d19146, d19142, g0, g1, g2, g3, g4, d19206, f19130, g7, g11, g12, g17, g20, g24, d19053, g27, d19037, g36, g37, d19222, g38, g39, g40, d19158, g41, g42, d19131, g45, g46, d19154, d19069, g47, g48, g49, g55, g56, g57, d19228, d19174, d19194]
    · have f19401 : (x (-1) 3).toNat = 1 := by rw [h19226]; rfl
      have d19402 : (x 2 12).toNat = 0 := by
        have r19403 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e19404 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
        have e19405 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
        have b19406 := hb (x (-1) 3)
        have b19407 := hb (x 0 2)
        have b19408 := hb (x 1 13)
        have b19409 := hb (x 2 12)
        clear * - r19403 e19404 e19405 b19406 b19407 b19408 b19409 g22 g6 f19401
        omega
      have d19410 : (x 2 4).toNat = 0 := by
        have r19411 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
        have b19412 := hb (x 2 4)
        have b19413 := hb (x 2 12)
        clear * - r19411 b19412 b19413 d19402
        omega
      have d19414 : (x 2 4 && x 2 13).toNat = 0 := by
        have r19415 := hand1 (x 2 4) (x 2 13)
        have b19416 := hb (x 2 4)
        have b19417 := hb (x 2 4 && x 2 13)
        clear * - r19415 b19416 b19417 d19410
        omega
      have r19418 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19419 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19420 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19421 : (x (-5) 8).toNat + (x (-6) 1 && x (-6) 9).toNat + (x (-7) 2 && x (-7) 10).toNat + (x (-8) 3 && x (-8) 11).toNat + (x (-9) 4 && x (-9) 12).toNat + (x (-10) 5 && x (-10) 13).toNat + (x (-11) 6 && x (-11) 14).toNat + (x (-12) 7).toNat = 1 := by have q := hd8 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19422 : (x (-6) 1 && x (-6) 9).toNat = (x (-6) 9).toNat := handr _ _ (fun h => hp9 (-6) (h))
      have e19423 : (x (-7) 2 && x (-7) 10).toNat = (x (-7) 10).toNat := handr _ _ (fun h => hp10 (-7) (h))
      have e19424 : (x (-8) 3 && x (-8) 11).toNat = (x (-8) 11).toNat := handr _ _ (fun h => hp11 (-8) (h))
      have e19425 : (x (-9) 4 && x (-9) 12).toNat = (x (-9) 4).toNat := handl _ _ (fun h => hp4 (-9) (h))
      have e19426 : (x (-10) 5 && x (-10) 13).toNat = (x (-10) 5).toNat := handl _ _ (fun h => hp5 (-10) (h))
      have e19427 : (x (-11) 6 && x (-11) 14).toNat = (x (-11) 6).toNat := handl _ _ (fun h => hp6 (-11) (h))
      have r19428 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19429 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
      have e19430 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
      have e19431 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
      have e19432 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
      have e19433 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
      have e19434 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
      have r19435 : 1 ≤ (x 12 3).toNat + (x 11 1 && x 11 4).toNat + (x 10 2 && x 10 5).toNat + (x 9 3 && x 9 6).toNat + (x 8 4 && x 8 7).toNat + (x 7 5 && x 7 8).toNat + (x 6 6 && x 6 9).toNat + (x 5 7 && x 5 10).toNat + (x 4 8 && x 4 11).toNat + (x 3 9 && x 3 12).toNat + (x 2 10 && x 2 13).toNat + (x 1 11 && x 1 14).toNat + (x 0 12).toNat := by have q := hcov3 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19436 : 1 ≤ (x 3 4).toNat + (x 2 1 && x 2 5).toNat + (x 1 2 && x 1 6).toNat + (x 0 3 && x 0 7).toNat + (x (-1) 4 && x (-1) 8).toNat + (x (-2) 5 && x (-2) 9).toNat + (x (-3) 6 && x (-3) 10).toNat + (x (-4) 7 && x (-4) 11).toNat + (x (-5) 8 && x (-5) 12).toNat + (x (-6) 9 && x (-6) 13).toNat + (x (-7) 10 && x (-7) 14).toNat + (x (-8) 11).toNat := by have q := hcov4 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19437 : (x 2 1 && x 2 5).toNat = (x 2 5).toNat := handr _ _ (fun h => hp13 2 (hp5 2 (h)))
      have e19438 : (x (-7) 10 && x (-7) 14).toNat = (x (-7) 10).toNat := handl _ _ (fun h => hp2 (-7) (hp10 (-7) (h)))
      have r19439 : 1 ≤ (x (-5) 9).toNat + (x (-6) 1 && x (-6) 10).toNat + (x (-7) 2 && x (-7) 11).toNat + (x (-8) 3 && x (-8) 12).toNat + (x (-9) 4 && x (-9) 13).toNat + (x (-10) 5 && x (-10) 14).toNat + (x (-11) 6).toNat := by have q := hcov9 (-5); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19440 : 1 ≤ (x 3 9).toNat + (x 2 1 && x 2 10).toNat + (x 1 2 && x 1 11).toNat + (x 0 3 && x 0 12).toNat + (x (-1) 4 && x (-1) 13).toNat + (x (-2) 5 && x (-2) 14).toNat + (x (-3) 6).toNat := by have q := hcov9 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19441 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19442 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19443 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r19444 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
      have r19445 := hand2 (x 11 1) (x 11 4)
      have r19446 := hand2 (x 10 2) (x 10 5)
      have r19447 := hand2 (x 9 3) (x 9 6)
      have r19448 := hand2 (x 8 4) (x 8 7)
      have r19449 := hand2 (x 7 5) (x 7 8)
      have r19450 := hand2 (x 6 6) (x 6 9)
      have r19451 := hand2 (x 5 7) (x 5 10)
      have r19452 := hand1 (x (-5) 8) (x (-5) 12)
      have r19453 := hand2 (x (-6) 1) (x (-6) 10)
      have r19454 := hand1 (x (-9) 4) (x (-9) 13)
      have r19455 := hand1 (x (-10) 5) (x (-10) 14)
      have r19456 := hand1 (x (-1) 4) (x (-1) 13)
      have r19457 := hand2 (x 5 1) (x 5 10)
      have r19458 := hand2 (x 4 2) (x 4 11)
      have r19459 := hand1 (x 2 2) (x 2 13)
      have r19460 := hand1 (x 1 3) (x 1 14)
      have r19461 := hand2 (x (-10) 1) (x (-10) 14)
      linarith only [r19418, r19419, r19420, r19421, e19422, e19423, e19424, e19425, e19426, e19427, r19428, e19429, e19430, e19431, e19432, e19433, e19434, r19435, r19436, e19437, e19438, r19439, r19440, r19441, r19442, r19443, r19444, r19445, r19446, r19447, r19448, r19449, r19450, r19451, r19452, r19453, r19454, r19455, r19456, r19457, r19458, r19459, r19460, r19461, d19202, d19182, d19113, g2, d19097, g5, g7, g8, g10, g11, g14, g17, g23, g24, g25, g27, d19037, g29, d19033, g34, d19073, d19093, g36, g37, d19222, g38, g39, g40, d19158, d19178, d19198, d19069, g47, g48, g49, g53, d19414, g54, g65]
  · have f19554 : (x (-1) 11).toNat = 1 := by rw [h19129]; rfl
    have d19555 : (x (-1) 3).toNat = 1 := by
      have r19556 : (x (-1) 11).toNat ≤ (x (-1) 3).toNat := himp _ _ (hp11 (-1))
      have b19557 := hb (x (-1) 3)
      have b19558 := hb (x (-1) 11)
      clear * - r19556 b19557 b19558 f19554
      omega
    have d19559 : (x 2 12).toNat = 0 := by
      have r19560 : (x 2 12).toNat + (x 1 1 && x 1 13).toNat + (x 0 2 && x 0 14).toNat + (x (-1) 3).toNat = 1 := by have q := hd12 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19561 : (x 1 1 && x 1 13).toNat = (x 1 13).toNat := handr _ _ (fun h => hp13 1 (h))
      have e19562 : (x 0 2 && x 0 14).toNat = (x 0 2).toNat := handl _ _ (fun h => hp2 0 (h))
      have b19563 := hb (x (-1) 3)
      have b19564 := hb (x 0 2)
      have b19565 := hb (x 1 13)
      have b19566 := hb (x 2 12)
      clear * - r19560 e19561 e19562 b19563 b19564 b19565 b19566 g22 g6 d19555
      omega
    have d19567 : (x 2 1 && x 2 12).toNat = 0 := by
      have r19568 := hand2 (x 2 1) (x 2 12)
      have b19569 := hb (x 2 12)
      have b19570 := hb (x 2 1 && x 2 12)
      clear * - r19568 b19569 b19570 d19559
      omega
    have d19571 : (x 2 3 && x 2 12).toNat = 0 := by
      have r19572 := hand2 (x 2 3) (x 2 12)
      have b19573 := hb (x 2 12)
      have b19574 := hb (x 2 3 && x 2 12)
      clear * - r19572 b19573 b19574 d19559
      omega
    have d19575 : (x 2 12 && x 2 13).toNat = 0 := by
      have r19576 := hand1 (x 2 12) (x 2 13)
      have b19577 := hb (x 2 12)
      have b19578 := hb (x 2 12 && x 2 13)
      clear * - r19576 b19577 b19578 d19559
      omega
    have d19579 : (x 2 4).toNat = 0 := by
      have r19580 : (x 2 4).toNat ≤ (x 2 12).toNat := himp _ _ (hp4 2)
      have b19581 := hb (x 2 4)
      have b19582 := hb (x 2 12)
      clear * - r19580 b19581 b19582 d19559
      omega
    have d19583 : (x 2 4 && x 2 13).toNat = 0 := by
      have r19584 := hand1 (x 2 4) (x 2 13)
      have b19585 := hb (x 2 4)
      have b19586 := hb (x 2 4 && x 2 13)
      clear * - r19584 b19585 b19586 d19579
      omega
    have d19587 : (x 2 8).toNat = 0 := by
      have r19588 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19589 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e19590 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e19591 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e19592 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e19593 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e19594 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b19595 := hb (x (-5) 7)
      have b19596 := hb (x (-4) 6)
      have b19597 := hb (x (-3) 5)
      have b19598 := hb (x (-2) 4)
      have b19599 := hb (x (-1) 11)
      have b19600 := hb (x 0 10)
      have b19601 := hb (x 1 9)
      have b19602 := hb (x 2 8)
      clear * - r19588 e19589 e19590 e19591 e19592 e19593 e19594 b19595 b19596 b19597 b19598 b19599 b19600 b19601 b19602 g20 g12 f19554
      omega
    have d19603 : (x 2 8 && x 2 13).toNat = 0 := by
      have r19604 := hand1 (x 2 8) (x 2 13)
      have b19605 := hb (x 2 8)
      have b19606 := hb (x 2 8 && x 2 13)
      clear * - r19604 b19605 b19606 d19587
      omega
    have d19607 : (x (-2) 4).toNat = 0 := by
      have r19608 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19609 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e19610 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e19611 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e19612 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e19613 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e19614 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b19615 := hb (x (-5) 7)
      have b19616 := hb (x (-4) 6)
      have b19617 := hb (x (-3) 5)
      have b19618 := hb (x (-2) 4)
      have b19619 := hb (x (-1) 11)
      have b19620 := hb (x 0 10)
      have b19621 := hb (x 1 9)
      have b19622 := hb (x 2 8)
      clear * - r19608 e19609 e19610 e19611 e19612 e19613 e19614 b19615 b19616 b19617 b19618 b19619 b19620 b19621 b19622 d19587 g20 g12 f19554
      omega
    have d19623 : (x (-2) 4 && x (-2) 8).toNat = 0 := by
      have r19624 := hand1 (x (-2) 4) (x (-2) 8)
      have b19625 := hb (x (-2) 4)
      have b19626 := hb (x (-2) 4 && x (-2) 8)
      clear * - r19624 b19625 b19626 d19607
      omega
    have d19627 : (x (-3) 5).toNat = 0 := by
      have r19628 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19629 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e19630 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e19631 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e19632 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e19633 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e19634 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b19635 := hb (x (-5) 7)
      have b19636 := hb (x (-4) 6)
      have b19637 := hb (x (-3) 5)
      have b19638 := hb (x (-2) 4)
      have b19639 := hb (x (-1) 11)
      have b19640 := hb (x 0 10)
      have b19641 := hb (x 1 9)
      have b19642 := hb (x 2 8)
      clear * - r19628 e19629 e19630 e19631 e19632 e19633 e19634 b19635 b19636 b19637 b19638 b19639 b19640 b19641 b19642 d19587 g20 g12 f19554 d19607
      omega
    have d19643 : (x (-3) 5 && x (-3) 9).toNat = 0 := by
      have r19644 := hand1 (x (-3) 5) (x (-3) 9)
      have b19645 := hb (x (-3) 5)
      have b19646 := hb (x (-3) 5 && x (-3) 9)
      clear * - r19644 b19645 b19646 d19627
      omega
    have d19647 : (x (-4) 6).toNat = 0 := by
      have r19648 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19649 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e19650 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e19651 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e19652 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e19653 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e19654 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b19655 := hb (x (-5) 7)
      have b19656 := hb (x (-4) 6)
      have b19657 := hb (x (-3) 5)
      have b19658 := hb (x (-2) 4)
      have b19659 := hb (x (-1) 11)
      have b19660 := hb (x 0 10)
      have b19661 := hb (x 1 9)
      have b19662 := hb (x 2 8)
      clear * - r19648 e19649 e19650 e19651 e19652 e19653 e19654 b19655 b19656 b19657 b19658 b19659 b19660 b19661 b19662 d19587 g20 g12 f19554 d19607 d19627
      omega
    have d19663 : (x (-4) 6 && x (-4) 10).toNat = 0 := by
      have r19664 := hand1 (x (-4) 6) (x (-4) 10)
      have b19665 := hb (x (-4) 6)
      have b19666 := hb (x (-4) 6 && x (-4) 10)
      clear * - r19664 b19665 b19666 d19647
      omega
    have d19667 : (x (-5) 7).toNat = 0 := by
      have r19668 : (x 2 8).toNat + (x 1 1 && x 1 9).toNat + (x 0 2 && x 0 10).toNat + (x (-1) 3 && x (-1) 11).toNat + (x (-2) 4 && x (-2) 12).toNat + (x (-3) 5 && x (-3) 13).toNat + (x (-4) 6 && x (-4) 14).toNat + (x (-5) 7).toNat = 1 := by have q := hd8 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e19669 : (x 1 1 && x 1 9).toNat = (x 1 9).toNat := handr _ _ (fun h => hp9 1 (h))
      have e19670 : (x 0 2 && x 0 10).toNat = (x 0 10).toNat := handr _ _ (fun h => hp10 0 (h))
      have e19671 : (x (-1) 3 && x (-1) 11).toNat = (x (-1) 11).toNat := handr _ _ (fun h => hp11 (-1) (h))
      have e19672 : (x (-2) 4 && x (-2) 12).toNat = (x (-2) 4).toNat := handl _ _ (fun h => hp4 (-2) (h))
      have e19673 : (x (-3) 5 && x (-3) 13).toNat = (x (-3) 5).toNat := handl _ _ (fun h => hp5 (-3) (h))
      have e19674 : (x (-4) 6 && x (-4) 14).toNat = (x (-4) 6).toNat := handl _ _ (fun h => hp6 (-4) (h))
      have b19675 := hb (x (-5) 7)
      have b19676 := hb (x (-4) 6)
      have b19677 := hb (x (-3) 5)
      have b19678 := hb (x (-2) 4)
      have b19679 := hb (x (-1) 11)
      have b19680 := hb (x 0 10)
      have b19681 := hb (x 1 9)
      have b19682 := hb (x 2 8)
      clear * - r19668 e19669 e19670 e19671 e19672 e19673 e19674 b19675 b19676 b19677 b19678 b19679 b19680 b19681 b19682 d19587 g20 g12 f19554 d19607 d19627 d19647
      omega
    have d19683 : (x (-5) 7 && x (-5) 11).toNat = 0 := by
      have r19684 := hand1 (x (-5) 7) (x (-5) 11)
      have b19685 := hb (x (-5) 7)
      have b19686 := hb (x (-5) 7 && x (-5) 11)
      clear * - r19684 b19685 b19686 d19667
      omega
    cases h19687 : x 1 3
    · have f19688 : (x 1 3).toNat = 0 := by rw [h19687]; rfl
      have d19689 : (x 1 3 && x 1 14).toNat = 0 := by
        have r19690 := hand1 (x 1 3) (x 1 14)
        have b19691 := hb (x 1 3)
        have b19692 := hb (x 1 3 && x 1 14)
        clear * - r19690 b19691 b19692 f19688
        omega
      cases h19693 : x (-1) 4
      · have f19694 : (x (-1) 4).toNat = 0 := by rw [h19693]; rfl
        have d19695 : (x 3 11).toNat = 1 := by
          have r19696 : 1 ≤ (x 3 11).toNat + (x 2 1 && x 2 12).toNat + (x 1 2 && x 1 13).toNat + (x 0 3 && x 0 14).toNat + (x (-1) 4).toNat := by have q := hcov11 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19697 := hb (x (-1) 4)
          have b19698 := hb (x 3 11)
          have b19699 := hb (x 2 1 && x 2 12)
          have b19700 := hb (x 1 2 && x 1 13)
          have b19701 := hb (x 0 3 && x 0 14)
          clear * - r19696 b19697 b19698 b19699 b19700 b19701 d19567 g63 g64 f19694
          omega
        have d19702 : (x 3 3).toNat = 1 := by
          have r19703 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
          have b19704 := hb (x 3 3)
          have b19705 := hb (x 3 11)
          clear * - r19703 b19704 b19705 d19695
          omega
        have d19706 : (x 6 12).toNat = 0 := by
          have r19707 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19708 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e19709 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b19710 := hb (x 3 3)
          have b19711 := hb (x 4 2)
          have b19712 := hb (x 5 13)
          have b19713 := hb (x 6 12)
          clear * - r19707 e19708 e19709 b19710 b19711 b19712 b19713 d19702
          omega
        have d19714 : (x 6 1 && x 6 12).toNat = 0 := by
          have r19715 := hand2 (x 6 1) (x 6 12)
          have b19716 := hb (x 6 12)
          have b19717 := hb (x 6 1 && x 6 12)
          clear * - r19715 b19716 b19717 d19706
          omega
        have d19718 : (x 6 4).toNat = 0 := by
          have r19719 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
          have b19720 := hb (x 6 4)
          have b19721 := hb (x 6 12)
          clear * - r19719 b19720 b19721 d19706
          omega
        have d19722 : (x 5 13).toNat = 0 := by
          have r19723 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19724 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e19725 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b19726 := hb (x 3 3)
          have b19727 := hb (x 4 2)
          have b19728 := hb (x 5 13)
          have b19729 := hb (x 6 12)
          clear * - r19723 e19724 e19725 b19726 b19727 b19728 b19729 d19706 d19702
          omega
        have d19730 : (x 5 2 && x 5 13).toNat = 0 := by
          have r19731 := hand2 (x 5 2) (x 5 13)
          have b19732 := hb (x 5 13)
          have b19733 := hb (x 5 2 && x 5 13)
          clear * - r19731 b19732 b19733 d19722
          omega
        have d19734 : (x 4 1 && x 4 14).toNat = 1 := by
          have r19735 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19736 := hb (x 3 2)
          have b19737 := hb (x 5 13)
          have b19738 := hb (x 4 1 && x 4 14)
          clear * - r19735 b19736 b19737 b19738 d19722 g26
          omega
        have d19739 : (x 4 1).toNat = 1 := by
          have r19740 := hand1 (x 4 1) (x 4 14)
          have b19741 := hb (x 4 1)
          have b19742 := hb (x 4 1 && x 4 14)
          clear * - r19740 b19741 b19742 d19734
          omega
        have d19743 : (x 5 14).toNat = 0 := by
          have r19744 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19745 := hb (x 4 1)
          have b19746 := hb (x 5 14)
          clear * - r19744 b19745 b19746 d19739
          omega
        have d19747 : (x 5 1 && x 5 14).toNat = 0 := by
          have r19748 := hand2 (x 5 1) (x 5 14)
          have b19749 := hb (x 5 14)
          have b19750 := hb (x 5 1 && x 5 14)
          clear * - r19748 b19749 b19750 d19743
          omega
        have d19751 : (x 5 2).toNat = 0 := by
          have r19752 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
          have b19753 := hb (x 5 2)
          have b19754 := hb (x 5 14)
          clear * - r19752 b19753 b19754 d19743
          omega
        have d19755 : (x 4 2).toNat = 0 := by
          have r19756 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19757 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e19758 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have b19759 := hb (x 3 3)
          have b19760 := hb (x 4 2)
          have b19761 := hb (x 5 13)
          have b19762 := hb (x 6 12)
          clear * - r19756 e19757 e19758 b19759 b19760 b19761 b19762 d19706 d19722 d19702
          omega
        have d19763 : (x 4 2 && x 4 13).toNat = 0 := by
          have r19764 := hand1 (x 4 2) (x 4 13)
          have b19765 := hb (x 4 2)
          have b19766 := hb (x 4 2 && x 4 13)
          clear * - r19764 b19765 b19766 d19755
          omega
        have d19767 : (x 6 13).toNat = 1 := by
          have r19768 : 1 ≤ (x 6 13).toNat + (x 5 1 && x 5 14).toNat + (x 4 2).toNat := by have q := hcov13 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19769 := hb (x 4 2)
          have b19770 := hb (x 6 13)
          have b19771 := hb (x 5 1 && x 5 14)
          clear * - r19768 b19769 b19770 b19771 d19747 d19755
          omega
        have d19772 : (x 6 1).toNat = 1 := by
          have r19773 : (x 6 13).toNat ≤ (x 6 1).toNat := himp _ _ (hp13 6)
          have b19774 := hb (x 6 1)
          have b19775 := hb (x 6 13)
          clear * - r19773 b19774 b19775 d19767
          omega
        have d19776 : (x 7 14).toNat = 0 := by
          have r19777 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19778 := hb (x 6 1)
          have b19779 := hb (x 7 14)
          clear * - r19777 b19778 b19779 d19772
          omega
        have d19780 : (x 7 3 && x 7 14).toNat = 0 := by
          have r19781 := hand2 (x 7 3) (x 7 14)
          have b19782 := hb (x 7 14)
          have b19783 := hb (x 7 3 && x 7 14)
          clear * - r19781 b19782 b19783 d19776
          omega
        have d19784 : (x 7 2).toNat = 0 := by
          have r19785 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
          have b19786 := hb (x 7 2)
          have b19787 := hb (x 7 14)
          clear * - r19785 b19786 b19787 d19776
          omega
        have d19788 : (x 7 12).toNat = 0 := by
          have r19789 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19790 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e19791 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b19792 := hb (x 4 3)
          have b19793 := hb (x 5 2)
          have b19794 := hb (x 6 13)
          have b19795 := hb (x 7 12)
          clear * - r19789 e19790 e19791 b19792 b19793 b19794 b19795 d19767 d19751
          omega
        have d19796 : (x 7 4).toNat = 0 := by
          have r19797 : (x 7 4).toNat ≤ (x 7 12).toNat := himp _ _ (hp4 7)
          have b19798 := hb (x 7 4)
          have b19799 := hb (x 7 12)
          clear * - r19797 b19798 b19799 d19788
          omega
        have d19800 : (x 4 3).toNat = 0 := by
          have r19801 : (x 7 12).toNat + (x 6 1 && x 6 13).toNat + (x 5 2 && x 5 14).toNat + (x 4 3).toNat = 1 := by have q := hd12 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19802 : (x 6 1 && x 6 13).toNat = (x 6 13).toNat := handr _ _ (fun h => hp13 6 (h))
          have e19803 : (x 5 2 && x 5 14).toNat = (x 5 2).toNat := handl _ _ (fun h => hp2 5 (h))
          have b19804 := hb (x 4 3)
          have b19805 := hb (x 5 2)
          have b19806 := hb (x 6 13)
          have b19807 := hb (x 7 12)
          clear * - r19801 e19802 e19803 b19804 b19805 b19806 b19807 d19788 d19767 d19751
          omega
        have d19808 : (x 4 3 && x 4 14).toNat = 0 := by
          have r19809 := hand1 (x 4 3) (x 4 14)
          have b19810 := hb (x 4 3)
          have b19811 := hb (x 4 3 && x 4 14)
          clear * - r19809 b19810 b19811 d19800
          omega
        have d19812 : (x 7 11).toNat = 1 := by
          have r19813 : 1 ≤ (x 7 11).toNat + (x 6 1 && x 6 12).toNat + (x 5 2 && x 5 13).toNat + (x 4 3 && x 4 14).toNat + (x 3 4).toNat := by have q := hcov11 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19814 := hb (x 3 4)
          have b19815 := hb (x 7 11)
          have b19816 := hb (x 6 1 && x 6 12)
          have b19817 := hb (x 5 2 && x 5 13)
          have b19818 := hb (x 4 3 && x 4 14)
          clear * - r19813 b19814 b19815 b19816 b19817 b19818 d19714 d19730 d19808 g27
          omega
        have d19819 : (x 7 3).toNat = 1 := by
          have r19820 : (x 7 11).toNat ≤ (x 7 3).toNat := himp _ _ (hp11 7)
          have b19821 := hb (x 7 3)
          have b19822 := hb (x 7 11)
          clear * - r19820 b19821 b19822 d19812
          omega
        have d19823 : (x 10 12).toNat = 0 := by
          have r19824 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19825 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e19826 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b19827 := hb (x 7 3)
          have b19828 := hb (x 8 2)
          have b19829 := hb (x 9 13)
          have b19830 := hb (x 10 12)
          clear * - r19824 e19825 e19826 b19827 b19828 b19829 b19830 d19819
          omega
        have d19831 : (x 10 1 && x 10 12).toNat = 0 := by
          have r19832 := hand2 (x 10 1) (x 10 12)
          have b19833 := hb (x 10 12)
          have b19834 := hb (x 10 1 && x 10 12)
          clear * - r19832 b19833 b19834 d19823
          omega
        have d19835 : (x 10 4).toNat = 0 := by
          have r19836 : (x 10 4).toNat ≤ (x 10 12).toNat := himp _ _ (hp4 10)
          have b19837 := hb (x 10 4)
          have b19838 := hb (x 10 12)
          clear * - r19836 b19837 b19838 d19823
          omega
        have d19839 : (x 9 13).toNat = 0 := by
          have r19840 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19841 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e19842 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b19843 := hb (x 7 3)
          have b19844 := hb (x 8 2)
          have b19845 := hb (x 9 13)
          have b19846 := hb (x 10 12)
          clear * - r19840 e19841 e19842 b19843 b19844 b19845 b19846 d19823 d19819
          omega
        have d19847 : (x 9 2 && x 9 13).toNat = 0 := by
          have r19848 := hand2 (x 9 2) (x 9 13)
          have b19849 := hb (x 9 13)
          have b19850 := hb (x 9 2 && x 9 13)
          clear * - r19848 b19849 b19850 d19839
          omega
        have d19851 : (x 8 1 && x 8 14).toNat = 1 := by
          have r19852 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19853 := hb (x 7 2)
          have b19854 := hb (x 9 13)
          have b19855 := hb (x 8 1 && x 8 14)
          clear * - r19852 b19853 b19854 b19855 d19839 d19784
          omega
        have d19856 : (x 8 14).toNat = 1 := by
          have r19857 := hand2 (x 8 1) (x 8 14)
          have b19858 := hb (x 8 14)
          have b19859 := hb (x 8 1 && x 8 14)
          clear * - r19857 b19858 b19859 d19851
          omega
        have d19860 : (x 7 1).toNat = 0 := by
          have r19861 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19862 := hb (x 7 1)
          have b19863 := hb (x 8 14)
          clear * - r19861 b19862 b19863 d19856
          omega
        have d19864 : (x 7 13).toNat = 0 := by
          have r19865 : (x 7 13).toNat ≤ (x 7 1).toNat := himp _ _ (hp13 7)
          have b19866 := hb (x 7 1)
          have b19867 := hb (x 7 13)
          clear * - r19865 b19866 b19867 d19860
          omega
        have d19868 : (x 6 1 && x 6 14).toNat = 1 := by
          have r19869 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19870 := hb (x 5 2)
          have b19871 := hb (x 7 13)
          have b19872 := hb (x 6 1 && x 6 14)
          clear * - r19869 b19870 b19871 b19872 d19864 d19751
          omega
        have d19873 : (x 6 14).toNat = 1 := by
          have r19874 := hand2 (x 6 1) (x 6 14)
          have b19875 := hb (x 6 14)
          have b19876 := hb (x 6 1 && x 6 14)
          clear * - r19874 b19875 b19876 d19868
          omega
        have d19877 : (x 5 1).toNat = 0 := by
          have r19878 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19879 := hb (x 5 1)
          have b19880 := hb (x 6 14)
          clear * - r19878 b19879 b19880 d19873
          omega
        have d19881 : (x 5 1 && x 5 12).toNat = 0 := by
          have r19882 := hand1 (x 5 1) (x 5 12)
          have b19883 := hb (x 5 1)
          have b19884 := hb (x 5 1 && x 5 12)
          clear * - r19882 b19883 b19884 d19877
          omega
        have d19885 : (x 6 11).toNat = 1 := by
          have r19886 : 1 ≤ (x 6 11).toNat + (x 5 1 && x 5 12).toNat + (x 4 2 && x 4 13).toNat + (x 3 3 && x 3 14).toNat + (x 2 4).toNat := by have q := hcov11 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19887 := hb (x 2 4)
          have b19888 := hb (x 6 11)
          have b19889 := hb (x 5 1 && x 5 12)
          have b19890 := hb (x 4 2 && x 4 13)
          have b19891 := hb (x 3 3 && x 3 14)
          clear * - r19886 b19887 b19888 b19889 b19890 b19891 d19881 d19763 g67 d19579
          omega
        have d19892 : (x 6 3).toNat = 1 := by
          have r19893 : (x 6 11).toNat ≤ (x 6 3).toNat := himp _ _ (hp11 6)
          have b19894 := hb (x 6 3)
          have b19895 := hb (x 6 11)
          clear * - r19893 b19894 b19895 d19885
          omega
        have d19896 : (x 9 12).toNat = 0 := by
          have r19897 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19898 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e19899 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b19900 := hb (x 6 3)
          have b19901 := hb (x 7 2)
          have b19902 := hb (x 8 13)
          have b19903 := hb (x 9 12)
          clear * - r19897 e19898 e19899 b19900 b19901 b19902 b19903 d19784 d19892
          omega
        have d19904 : (x 9 1 && x 9 12).toNat = 0 := by
          have r19905 := hand2 (x 9 1) (x 9 12)
          have b19906 := hb (x 9 12)
          have b19907 := hb (x 9 1 && x 9 12)
          clear * - r19905 b19906 b19907 d19896
          omega
        have d19908 : (x 8 13).toNat = 0 := by
          have r19909 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19910 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
          have e19911 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
          have b19912 := hb (x 6 3)
          have b19913 := hb (x 7 2)
          have b19914 := hb (x 8 13)
          have b19915 := hb (x 9 12)
          clear * - r19909 e19910 e19911 b19912 b19913 b19914 b19915 d19896 d19784 d19892
          omega
        have d19916 : (x 8 2 && x 8 13).toNat = 0 := by
          have r19917 := hand2 (x 8 2) (x 8 13)
          have b19918 := hb (x 8 13)
          have b19919 := hb (x 8 2 && x 8 13)
          clear * - r19917 b19918 b19919 d19908
          omega
        have d19920 : (x 10 11).toNat = 1 := by
          have r19921 : 1 ≤ (x 10 11).toNat + (x 9 1 && x 9 12).toNat + (x 8 2 && x 8 13).toNat + (x 7 3 && x 7 14).toNat + (x 6 4).toNat := by have q := hcov11 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19922 := hb (x 6 4)
          have b19923 := hb (x 10 11)
          have b19924 := hb (x 9 1 && x 9 12)
          have b19925 := hb (x 8 2 && x 8 13)
          have b19926 := hb (x 7 3 && x 7 14)
          clear * - r19921 b19922 b19923 b19924 b19925 b19926 d19904 d19916 d19780 d19718
          omega
        have d19927 : (x 10 3).toNat = 1 := by
          have r19928 : (x 10 11).toNat ≤ (x 10 3).toNat := himp _ _ (hp11 10)
          have b19929 := hb (x 10 3)
          have b19930 := hb (x 10 11)
          clear * - r19928 b19929 b19930 d19920
          omega
        have d19931 : (x 13 12).toNat = 0 := by
          have r19932 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19933 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e19934 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b19935 := hb (x 10 3)
          have b19936 := hb (x 11 2)
          have b19937 := hb (x 12 13)
          have b19938 := hb (x 13 12)
          clear * - r19932 e19933 e19934 b19935 b19936 b19937 b19938 d19927
          omega
        have d19939 : (x 13 1 && x 13 12).toNat = 0 := by
          have r19940 := hand2 (x 13 1) (x 13 12)
          have b19941 := hb (x 13 12)
          have b19942 := hb (x 13 1 && x 13 12)
          clear * - r19940 b19941 b19942 d19931
          omega
        have d19943 : (x 12 13).toNat = 0 := by
          have r19944 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19945 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e19946 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b19947 := hb (x 10 3)
          have b19948 := hb (x 11 2)
          have b19949 := hb (x 12 13)
          have b19950 := hb (x 13 12)
          clear * - r19944 e19945 e19946 b19947 b19948 b19949 b19950 d19931 d19927
          omega
        have d19951 : (x 12 2 && x 12 13).toNat = 0 := by
          have r19952 := hand2 (x 12 2) (x 12 13)
          have b19953 := hb (x 12 13)
          have b19954 := hb (x 12 2 && x 12 13)
          clear * - r19952 b19953 b19954 d19943
          omega
        have d19955 : (x 11 2).toNat = 0 := by
          have r19956 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19957 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
          have e19958 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
          have b19959 := hb (x 10 3)
          have b19960 := hb (x 11 2)
          have b19961 := hb (x 12 13)
          have b19962 := hb (x 13 12)
          clear * - r19956 e19957 e19958 b19959 b19960 b19961 b19962 d19931 d19943 d19927
          omega
        have d19963 : (x 8 1).toNat = 1 := by
          have r19964 := hand1 (x 8 1) (x 8 14)
          have b19965 := hb (x 8 1)
          have b19966 := hb (x 8 1 && x 8 14)
          clear * - r19964 b19965 b19966 d19851
          omega
        have d19967 : (x 9 14).toNat = 0 := by
          have r19968 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19969 := hb (x 8 1)
          have b19970 := hb (x 9 14)
          clear * - r19968 b19969 b19970 d19963
          omega
        have d19971 : (x 9 1 && x 9 14).toNat = 0 := by
          have r19972 := hand2 (x 9 1) (x 9 14)
          have b19973 := hb (x 9 14)
          have b19974 := hb (x 9 1 && x 9 14)
          clear * - r19972 b19973 b19974 d19967
          omega
        have d19975 : (x 9 2).toNat = 0 := by
          have r19976 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
          have b19977 := hb (x 9 2)
          have b19978 := hb (x 9 14)
          clear * - r19976 b19977 b19978 d19967
          omega
        have d19979 : (x 8 2).toNat = 0 := by
          have r19980 : (x 10 12).toNat + (x 9 1 && x 9 13).toNat + (x 8 2 && x 8 14).toNat + (x 7 3).toNat = 1 := by have q := hd12 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e19981 : (x 9 1 && x 9 13).toNat = (x 9 13).toNat := handr _ _ (fun h => hp13 9 (h))
          have e19982 : (x 8 2 && x 8 14).toNat = (x 8 2).toNat := handl _ _ (fun h => hp2 8 (h))
          have b19983 := hb (x 7 3)
          have b19984 := hb (x 8 2)
          have b19985 := hb (x 9 13)
          have b19986 := hb (x 10 12)
          clear * - r19980 e19981 e19982 b19983 b19984 b19985 b19986 d19823 d19839 d19819
          omega
        have d19987 : (x 10 13).toNat = 1 := by
          have r19988 : 1 ≤ (x 10 13).toNat + (x 9 1 && x 9 14).toNat + (x 8 2).toNat := by have q := hcov13 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19989 := hb (x 8 2)
          have b19990 := hb (x 10 13)
          have b19991 := hb (x 9 1 && x 9 14)
          clear * - r19988 b19989 b19990 b19991 d19971 d19979
          omega
        have d19992 : (x 10 1).toNat = 1 := by
          have r19993 : (x 10 13).toNat ≤ (x 10 1).toNat := himp _ _ (hp13 10)
          have b19994 := hb (x 10 1)
          have b19995 := hb (x 10 13)
          clear * - r19993 b19994 b19995 d19987
          omega
        have d19996 : (x 11 14).toNat = 0 := by
          have r19997 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b19998 := hb (x 10 1)
          have b19999 := hb (x 11 14)
          clear * - r19997 b19998 b19999 d19992
          omega
        have d20000 : (x 11 1 && x 11 14).toNat = 0 := by
          have r20001 := hand2 (x 11 1) (x 11 14)
          have b20002 := hb (x 11 14)
          have b20003 := hb (x 11 1 && x 11 14)
          clear * - r20001 b20002 b20003 d19996
          omega
        have d20004 : (x 10 2).toNat = 1 := by
          have r20005 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20006 := hb (x 10 2)
          have b20007 := hb (x 12 13)
          have b20008 := hb (x 11 1 && x 11 14)
          clear * - r20005 b20006 b20007 b20008 d19943 d20000
          omega
        have d20009 : (x 12 12).toNat = 0 := by
          have r20010 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20011 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e20012 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b20013 := hb (x 9 3)
          have b20014 := hb (x 10 2)
          have b20015 := hb (x 11 13)
          have b20016 := hb (x 12 12)
          clear * - r20010 e20011 e20012 b20013 b20014 b20015 b20016 d20004
          omega
        have d20017 : (x 12 4).toNat = 0 := by
          have r20018 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
          have b20019 := hb (x 12 4)
          have b20020 := hb (x 12 12)
          clear * - r20018 b20019 b20020 d20009
          omega
        have d20021 : (x 12 4 && x 12 14).toNat = 0 := by
          have r20022 := hand1 (x 12 4) (x 12 14)
          have b20023 := hb (x 12 4)
          have b20024 := hb (x 12 4 && x 12 14)
          clear * - r20022 b20023 b20024 d20017
          omega
        have d20025 : (x 11 13).toNat = 0 := by
          have r20026 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20027 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
          have e20028 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
          have b20029 := hb (x 9 3)
          have b20030 := hb (x 10 2)
          have b20031 := hb (x 11 13)
          have b20032 := hb (x 12 12)
          clear * - r20026 e20027 e20028 b20029 b20030 b20031 b20032 d20009 d20004
          omega
        have d20033 : (x 11 5).toNat = 0 := by
          have r20034 : (x 11 5).toNat ≤ (x 11 13).toNat := himp _ _ (hp5 11)
          have b20035 := hb (x 11 5)
          have b20036 := hb (x 11 13)
          clear * - r20034 b20035 b20036 d20025
          omega
        have d20037 : (x 11 3 && x 11 14).toNat = 0 := by
          have r20038 := hand2 (x 11 3) (x 11 14)
          have b20039 := hb (x 11 14)
          have b20040 := hb (x 11 3 && x 11 14)
          clear * - r20038 b20039 b20040 d19996
          omega
        have d20041 : (x 14 11).toNat = 1 := by
          have r20042 : 1 ≤ (x 14 11).toNat + (x 13 1 && x 13 12).toNat + (x 12 2 && x 12 13).toNat + (x 11 3 && x 11 14).toNat + (x 10 4).toNat := by have q := hcov11 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20043 := hb (x 10 4)
          have b20044 := hb (x 14 11)
          have b20045 := hb (x 13 1 && x 13 12)
          have b20046 := hb (x 12 2 && x 12 13)
          have b20047 := hb (x 11 3 && x 11 14)
          clear * - r20042 b20043 b20044 b20045 b20046 b20047 d19939 d19951 d20037 d19835
          omega
        have d20048 : (x 14 3).toNat = 1 := by
          have r20049 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
          have b20050 := hb (x 14 3)
          have b20051 := hb (x 14 11)
          clear * - r20049 b20050 b20051 d20041
          omega
        have d20052 : (x 17 12).toNat = 0 := by
          have r20053 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20054 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e20055 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b20056 := hb (x 14 3)
          have b20057 := hb (x 15 2)
          have b20058 := hb (x 16 13)
          have b20059 := hb (x 17 12)
          clear * - r20053 e20054 e20055 b20056 b20057 b20058 b20059 d20048
          omega
        have d20060 : (x 16 13).toNat = 0 := by
          have r20061 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20062 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e20063 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b20064 := hb (x 14 3)
          have b20065 := hb (x 15 2)
          have b20066 := hb (x 16 13)
          have b20067 := hb (x 17 12)
          clear * - r20061 e20062 e20063 b20064 b20065 b20066 b20067 d20052 d20048
          omega
        have d20068 : (x 15 2).toNat = 0 := by
          have r20069 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20070 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
          have e20071 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
          have b20072 := hb (x 14 3)
          have b20073 := hb (x 15 2)
          have b20074 := hb (x 16 13)
          have b20075 := hb (x 17 12)
          clear * - r20069 e20070 e20071 b20072 b20073 b20074 b20075 d20052 d20060 d20048
          omega
        have d20076 : (x 11 12).toNat = 0 := by
          have r20077 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20078 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e20079 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b20080 := hb (x 8 3)
          have b20081 := hb (x 9 2)
          have b20082 := hb (x 10 13)
          have b20083 := hb (x 11 12)
          clear * - r20077 e20078 e20079 b20080 b20081 b20082 b20083 d19987 d19975
          omega
        have d20084 : (x 11 4).toNat = 0 := by
          have r20085 : (x 11 4).toNat ≤ (x 11 12).toNat := himp _ _ (hp4 11)
          have b20086 := hb (x 11 4)
          have b20087 := hb (x 11 12)
          clear * - r20085 b20086 b20087 d20076
          omega
        have d20088 : (x 8 3).toNat = 0 := by
          have r20089 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20090 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
          have e20091 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
          have b20092 := hb (x 8 3)
          have b20093 := hb (x 9 2)
          have b20094 := hb (x 10 13)
          have b20095 := hb (x 11 12)
          clear * - r20089 e20090 e20091 b20092 b20093 b20094 b20095 d20076 d19987 d19975
          omega
        have d20096 : (x 8 3 && x 8 14).toNat = 0 := by
          have r20097 := hand1 (x 8 3) (x 8 14)
          have b20098 := hb (x 8 3)
          have b20099 := hb (x 8 3 && x 8 14)
          clear * - r20097 b20098 b20099 d20088
          omega
        have d20100 : (x 11 11).toNat = 1 := by
          have r20101 : 1 ≤ (x 11 11).toNat + (x 10 1 && x 10 12).toNat + (x 9 2 && x 9 13).toNat + (x 8 3 && x 8 14).toNat + (x 7 4).toNat := by have q := hcov11 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20102 := hb (x 7 4)
          have b20103 := hb (x 11 11)
          have b20104 := hb (x 10 1 && x 10 12)
          have b20105 := hb (x 9 2 && x 9 13)
          have b20106 := hb (x 8 3 && x 8 14)
          clear * - r20101 b20102 b20103 b20104 b20105 b20106 d19831 d19847 d20096 d19796
          omega
        have d20107 : (x 11 3).toNat = 1 := by
          have r20108 : (x 11 11).toNat ≤ (x 11 3).toNat := himp _ _ (hp11 11)
          have b20109 := hb (x 11 3)
          have b20110 := hb (x 11 11)
          clear * - r20108 b20109 b20110 d20100
          omega
        have d20111 : (x 14 12).toNat = 0 := by
          have r20112 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20113 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e20114 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b20115 := hb (x 11 3)
          have b20116 := hb (x 12 2)
          have b20117 := hb (x 13 13)
          have b20118 := hb (x 14 12)
          clear * - r20112 e20113 e20114 b20115 b20116 b20117 b20118 d20107
          omega
        have d20119 : (x 14 1 && x 14 12).toNat = 0 := by
          have r20120 := hand2 (x 14 1) (x 14 12)
          have b20121 := hb (x 14 12)
          have b20122 := hb (x 14 1 && x 14 12)
          clear * - r20120 b20121 b20122 d20111
          omega
        have d20123 : (x 14 2 && x 14 12).toNat = 0 := by
          have r20124 := hand2 (x 14 2) (x 14 12)
          have b20125 := hb (x 14 12)
          have b20126 := hb (x 14 2 && x 14 12)
          clear * - r20124 b20125 b20126 d20111
          omega
        have d20127 : (x 13 13).toNat = 0 := by
          have r20128 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20129 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e20130 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b20131 := hb (x 11 3)
          have b20132 := hb (x 12 2)
          have b20133 := hb (x 13 13)
          have b20134 := hb (x 14 12)
          clear * - r20128 e20129 e20130 b20131 b20132 b20133 b20134 d20111 d20107
          omega
        have d20135 : (x 13 2 && x 13 13).toNat = 0 := by
          have r20136 := hand2 (x 13 2) (x 13 13)
          have b20137 := hb (x 13 13)
          have b20138 := hb (x 13 2 && x 13 13)
          clear * - r20136 b20137 b20138 d20127
          omega
        have d20139 : (x 13 3 && x 13 13).toNat = 0 := by
          have r20140 := hand2 (x 13 3) (x 13 13)
          have b20141 := hb (x 13 13)
          have b20142 := hb (x 13 3 && x 13 13)
          clear * - r20140 b20141 b20142 d20127
          omega
        have d20143 : (x 12 1 && x 12 14).toNat = 1 := by
          have r20144 : 1 ≤ (x 13 13).toNat + (x 12 1 && x 12 14).toNat + (x 11 2).toNat := by have q := hcov13 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20145 := hb (x 11 2)
          have b20146 := hb (x 13 13)
          have b20147 := hb (x 12 1 && x 12 14)
          clear * - r20144 b20145 b20146 b20147 d20127 d19955
          omega
        have d20148 : (x 12 1).toNat = 1 := by
          have r20149 := hand1 (x 12 1) (x 12 14)
          have b20150 := hb (x 12 1)
          have b20151 := hb (x 12 1 && x 12 14)
          clear * - r20149 b20150 b20151 d20143
          omega
        have d20152 : (x 13 14).toNat = 0 := by
          have r20153 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20154 := hb (x 12 1)
          have b20155 := hb (x 13 14)
          clear * - r20153 b20154 b20155 d20148
          omega
        have d20156 : (x 13 1 && x 13 14).toNat = 0 := by
          have r20157 := hand2 (x 13 1) (x 13 14)
          have b20158 := hb (x 13 14)
          have b20159 := hb (x 13 1 && x 13 14)
          clear * - r20157 b20158 b20159 d20152
          omega
        have d20160 : (x 13 2).toNat = 0 := by
          have r20161 : (x 13 2).toNat ≤ (x 13 14).toNat := himp _ _ (hp2 13)
          have b20162 := hb (x 13 2)
          have b20163 := hb (x 13 14)
          clear * - r20161 b20162 b20163 d20152
          omega
        have d20164 : (x 12 2).toNat = 0 := by
          have r20165 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20166 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
          have e20167 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
          have b20168 := hb (x 11 3)
          have b20169 := hb (x 12 2)
          have b20170 := hb (x 13 13)
          have b20171 := hb (x 14 12)
          clear * - r20165 e20166 e20167 b20168 b20169 b20170 b20171 d20111 d20127 d20107
          omega
        have d20172 : (x 14 13).toNat = 1 := by
          have r20173 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20174 := hb (x 12 2)
          have b20175 := hb (x 14 13)
          have b20176 := hb (x 13 1 && x 13 14)
          clear * - r20173 b20174 b20175 b20176 d20156 d20164
          omega
        have d20177 : (x 15 12).toNat = 0 := by
          have r20178 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20179 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e20180 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b20181 := hb (x 12 3)
          have b20182 := hb (x 13 2)
          have b20183 := hb (x 14 13)
          have b20184 := hb (x 15 12)
          clear * - r20178 e20179 e20180 b20181 b20182 b20183 b20184 d20172 d20160
          omega
        have d20185 : (x 12 3).toNat = 0 := by
          have r20186 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20187 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
          have e20188 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
          have b20189 := hb (x 12 3)
          have b20190 := hb (x 13 2)
          have b20191 := hb (x 14 13)
          have b20192 := hb (x 15 12)
          clear * - r20186 e20187 e20188 b20189 b20190 b20191 b20192 d20177 d20172 d20160
          omega
        have d20193 : (x 12 3 && x 12 14).toNat = 0 := by
          have r20194 := hand1 (x 12 3) (x 12 14)
          have b20195 := hb (x 12 3)
          have b20196 := hb (x 12 3 && x 12 14)
          clear * - r20194 b20195 b20196 d20185
          omega
        have d20197 : (x 15 11).toNat = 1 := by
          have r20198 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20199 := hb (x 11 4)
          have b20200 := hb (x 15 11)
          have b20201 := hb (x 14 1 && x 14 12)
          have b20202 := hb (x 13 2 && x 13 13)
          have b20203 := hb (x 12 3 && x 12 14)
          clear * - r20198 b20199 b20200 b20201 b20202 b20203 d20119 d20135 d20193 d20084
          omega
        have d20204 : (x 15 3).toNat = 1 := by
          have r20205 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
          have b20206 := hb (x 15 3)
          have b20207 := hb (x 15 11)
          clear * - r20205 b20206 b20207 d20197
          omega
        have d20208 : (x 18 12).toNat = 0 := by
          have r20209 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20210 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
          have e20211 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
          have b20212 := hb (x 15 3)
          have b20213 := hb (x 16 2)
          have b20214 := hb (x 17 13)
          have b20215 := hb (x 18 12)
          clear * - r20209 e20210 e20211 b20212 b20213 b20214 b20215 d20204
          omega
        have d20216 : (x 17 13).toNat = 0 := by
          have r20217 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20218 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
          have e20219 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
          have b20220 := hb (x 15 3)
          have b20221 := hb (x 16 2)
          have b20222 := hb (x 17 13)
          have b20223 := hb (x 18 12)
          clear * - r20217 e20218 e20219 b20220 b20221 b20222 b20223 d20208 d20204
          omega
        have d20224 : (x 16 1 && x 16 14).toNat = 1 := by
          have r20225 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20226 := hb (x 15 2)
          have b20227 := hb (x 17 13)
          have b20228 := hb (x 16 1 && x 16 14)
          clear * - r20225 b20226 b20227 b20228 d20216 d20068
          omega
        have d20229 : (x 16 14).toNat = 1 := by
          have r20230 := hand2 (x 16 1) (x 16 14)
          have b20231 := hb (x 16 14)
          have b20232 := hb (x 16 1 && x 16 14)
          clear * - r20230 b20231 b20232 d20224
          omega
        have d20233 : (x 15 1).toNat = 0 := by
          have r20234 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have b20235 := hb (x 15 1)
          have b20236 := hb (x 16 14)
          clear * - r20234 b20235 b20236 d20229
          omega
        have d20237 : (x 15 1 && x 15 11).toNat = 0 := by
          have r20238 := hand1 (x 15 1) (x 15 11)
          have b20239 := hb (x 15 1)
          have b20240 := hb (x 15 1 && x 15 11)
          clear * - r20238 b20239 b20240 d20233
          omega
        have d20241 : (x 16 2).toNat = 0 := by
          have r20242 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20243 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
          have e20244 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
          have b20245 := hb (x 15 3)
          have b20246 := hb (x 16 2)
          have b20247 := hb (x 17 13)
          have b20248 := hb (x 18 12)
          clear * - r20242 e20243 e20244 b20245 b20246 b20247 b20248 d20208 d20216 d20204
          omega
        have d20249 : (x 16 10).toNat = 0 := by
          have r20250 : (x 16 10).toNat ≤ (x 16 2).toNat := himp _ _ (hp10 16)
          have b20251 := hb (x 16 2)
          have b20252 := hb (x 16 10)
          clear * - r20250 b20251 b20252 d20241
          omega
        have r20253 : 1 ≤ (x 16 10).toNat + (x 15 1 && x 15 11).toNat + (x 14 2 && x 14 12).toNat + (x 13 3 && x 13 13).toNat + (x 12 4 && x 12 14).toNat + (x 11 5).toNat := by have q := hcov10 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b20254 := hb (x 11 5)
        have b20255 := hb (x 16 10)
        have b20256 := hb (x 15 1 && x 15 11)
        have b20257 := hb (x 14 2 && x 14 12)
        have b20258 := hb (x 13 3 && x 13 13)
        have b20259 := hb (x 12 4 && x 12 14)
        linarith only [r20253, b20254, b20255, b20256, b20257, b20258, b20259, d20249, d20237, d20123, d20139, d20021, d20033]
      · have f20260 : (x (-1) 4).toNat = 1 := by rw [h19693]; rfl
        have d20261 : (x 3 8).toNat = 0 := by
          have r20262 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20263 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e20264 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e20265 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e20266 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e20267 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e20268 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b20269 := hb (x (-4) 7)
          have b20270 := hb (x (-3) 6)
          have b20271 := hb (x (-2) 5)
          have b20272 := hb (x (-1) 4)
          have b20273 := hb (x 0 11)
          have b20274 := hb (x 1 10)
          have b20275 := hb (x 2 9)
          have b20276 := hb (x 3 8)
          clear * - r20262 e20263 e20264 e20265 e20266 e20267 e20268 b20269 b20270 b20271 b20272 b20273 b20274 b20275 b20276 g21 g13 f20260 g2
          omega
        have d20277 : (x 2 9).toNat = 0 := by
          have r20278 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20279 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e20280 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e20281 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e20282 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e20283 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e20284 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b20285 := hb (x (-4) 7)
          have b20286 := hb (x (-3) 6)
          have b20287 := hb (x (-2) 5)
          have b20288 := hb (x (-1) 4)
          have b20289 := hb (x 0 11)
          have b20290 := hb (x 1 10)
          have b20291 := hb (x 2 9)
          have b20292 := hb (x 3 8)
          clear * - r20278 e20279 e20280 e20281 e20282 e20283 e20284 b20285 b20286 b20287 b20288 b20289 b20290 b20291 b20292 d20261 g21 g13 f20260 g2
          omega
        have d20293 : (x (-3) 6).toNat = 0 := by
          have r20294 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20295 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e20296 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e20297 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e20298 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e20299 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e20300 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b20301 := hb (x (-4) 7)
          have b20302 := hb (x (-3) 6)
          have b20303 := hb (x (-2) 5)
          have b20304 := hb (x (-1) 4)
          have b20305 := hb (x 0 11)
          have b20306 := hb (x 1 10)
          have b20307 := hb (x 2 9)
          have b20308 := hb (x 3 8)
          clear * - r20294 e20295 e20296 e20297 e20298 e20299 e20300 b20301 b20302 b20303 b20304 b20305 b20306 b20307 b20308 d20261 d20277 g21 g13 f20260 g2
          omega
        have d20309 : (x (-4) 7).toNat = 0 := by
          have r20310 : (x 3 8).toNat + (x 2 1 && x 2 9).toNat + (x 1 2 && x 1 10).toNat + (x 0 3 && x 0 11).toNat + (x (-1) 4 && x (-1) 12).toNat + (x (-2) 5 && x (-2) 13).toNat + (x (-3) 6 && x (-3) 14).toNat + (x (-4) 7).toNat = 1 := by have q := hd8 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20311 : (x 2 1 && x 2 9).toNat = (x 2 9).toNat := handr _ _ (fun h => hp9 2 (h))
          have e20312 : (x 1 2 && x 1 10).toNat = (x 1 10).toNat := handr _ _ (fun h => hp10 1 (h))
          have e20313 : (x 0 3 && x 0 11).toNat = (x 0 11).toNat := handr _ _ (fun h => hp11 0 (h))
          have e20314 : (x (-1) 4 && x (-1) 12).toNat = (x (-1) 4).toNat := handl _ _ (fun h => hp4 (-1) (h))
          have e20315 : (x (-2) 5 && x (-2) 13).toNat = (x (-2) 5).toNat := handl _ _ (fun h => hp5 (-2) (h))
          have e20316 : (x (-3) 6 && x (-3) 14).toNat = (x (-3) 6).toNat := handl _ _ (fun h => hp6 (-3) (h))
          have b20317 := hb (x (-4) 7)
          have b20318 := hb (x (-3) 6)
          have b20319 := hb (x (-2) 5)
          have b20320 := hb (x (-1) 4)
          have b20321 := hb (x 0 11)
          have b20322 := hb (x 1 10)
          have b20323 := hb (x 2 9)
          have b20324 := hb (x 3 8)
          clear * - r20310 e20311 e20312 e20313 e20314 e20315 e20316 b20317 b20318 b20319 b20320 b20321 b20322 b20323 b20324 d20261 d20277 g21 g13 f20260 g2 d20293
          omega
        cases h20325 : x (-1) 6
        · have f20326 : (x (-1) 6).toNat = 0 := by rw [h20325]; rfl
          cases h20327 : x 1 6
          · have f20328 : (x 1 6).toNat = 0 := by rw [h20327]; rfl
            cases h20329 : x (-1) 7
            · have f20330 : (x (-1) 7).toNat = 0 := by rw [h20329]; rfl
              have d20331 : (x (-1) 3 && x (-1) 7).toNat = 0 := by
                have r20332 := hand2 (x (-1) 3) (x (-1) 7)
                have b20333 := hb (x (-1) 7)
                have b20334 := hb (x (-1) 3 && x (-1) 7)
                clear * - r20332 b20333 b20334 f20330
                omega
              have r20335 : (x 2 1).toNat + (x 1 2).toNat + (x 0 3).toNat + (x (-1) 4).toNat + (x (-2) 5).toNat + (x (-3) 6).toNat + (x (-4) 7).toNat + (x (-5) 8).toNat + (x (-6) 9).toNat + (x (-7) 10).toNat + (x (-8) 11).toNat + (x (-9) 12).toNat + (x (-10) 13).toNat + (x (-11) 14).toNat = 3 := by have q := hcount 3; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20336 : (x 3 1).toNat + (x 2 2).toNat + (x 1 3).toNat + (x 0 4).toNat + (x (-1) 5).toNat + (x (-2) 6).toNat + (x (-3) 7).toNat + (x (-4) 8).toNat + (x (-5) 9).toNat + (x (-6) 10).toNat + (x (-7) 11).toNat + (x (-8) 12).toNat + (x (-9) 13).toNat + (x (-10) 14).toNat = 3 := by have q := hcount 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20337 : (x 5 1).toNat + (x 4 2).toNat + (x 3 3).toNat + (x 2 4).toNat + (x 1 5).toNat + (x 0 6).toNat + (x (-1) 7).toNat + (x (-2) 8).toNat + (x (-3) 9).toNat + (x (-4) 10).toNat + (x (-5) 11).toNat + (x (-6) 12).toNat + (x (-7) 13).toNat + (x (-8) 14).toNat = 3 := by have q := hcount 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20338 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20339 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20340 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
              have e20341 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
              have e20342 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
              have e20343 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
              have e20344 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
              have e20345 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
              have r20346 : (x (-2) 8).toNat + (x (-3) 1 && x (-3) 9).toNat + (x (-4) 2 && x (-4) 10).toNat + (x (-5) 3 && x (-5) 11).toNat + (x (-6) 4 && x (-6) 12).toNat + (x (-7) 5 && x (-7) 13).toNat + (x (-8) 6 && x (-8) 14).toNat + (x (-9) 7).toNat = 1 := by have q := hd8 (-2); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20347 : (x (-3) 1 && x (-3) 9).toNat = (x (-3) 9).toNat := handr _ _ (fun h => hp9 (-3) (h))
              have e20348 : (x (-4) 2 && x (-4) 10).toNat = (x (-4) 10).toNat := handr _ _ (fun h => hp10 (-4) (h))
              have e20349 : (x (-5) 3 && x (-5) 11).toNat = (x (-5) 11).toNat := handr _ _ (fun h => hp11 (-5) (h))
              have e20350 : (x (-6) 4 && x (-6) 12).toNat = (x (-6) 4).toNat := handl _ _ (fun h => hp4 (-6) (h))
              have e20351 : (x (-7) 5 && x (-7) 13).toNat = (x (-7) 5).toNat := handl _ _ (fun h => hp5 (-7) (h))
              have e20352 : (x (-8) 6 && x (-8) 14).toNat = (x (-8) 6).toNat := handl _ _ (fun h => hp6 (-8) (h))
              have r20353 : (x (-6) 12).toNat + (x (-7) 1 && x (-7) 13).toNat + (x (-8) 2 && x (-8) 14).toNat + (x (-9) 3).toNat = 1 := by have q := hd12 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20354 : (x (-7) 1 && x (-7) 13).toNat = (x (-7) 13).toNat := handr _ _ (fun h => hp13 (-7) (h))
              have e20355 : (x (-8) 2 && x (-8) 14).toNat = (x (-8) 2).toNat := handl _ _ (fun h => hp2 (-8) (h))
              have r20356 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20357 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
              have e20358 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
              have r20359 : (x (-8) 14).toNat + (x (-9) 1).toNat = 1 := by have q := hd14 (-8); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20360 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20361 : (x 6 14).toNat + (x 5 1).toNat = 1 := by have q := hd14 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20362 : 1 ≤ (x 12 3).toNat + (x 11 1 && x 11 4).toNat + (x 10 2 && x 10 5).toNat + (x 9 3 && x 9 6).toNat + (x 8 4 && x 8 7).toNat + (x 7 5 && x 7 8).toNat + (x 6 6 && x 6 9).toNat + (x 5 7 && x 5 10).toNat + (x 4 8 && x 4 11).toNat + (x 3 9 && x 3 12).toNat + (x 2 10 && x 2 13).toNat + (x 1 11 && x 1 14).toNat + (x 0 12).toNat := by have q := hcov3 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20363 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20364 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
              have e20365 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
              have r20366 : 1 ≤ (x (-6) 9).toNat + (x (-7) 1 && x (-7) 10).toNat + (x (-8) 2 && x (-8) 11).toNat + (x (-9) 3 && x (-9) 12).toNat + (x (-10) 4 && x (-10) 13).toNat + (x (-11) 5 && x (-11) 14).toNat + (x (-12) 6).toNat := by have q := hcov9 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20367 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20368 : 1 ≤ (x (-6) 10).toNat + (x (-7) 1 && x (-7) 11).toNat + (x (-8) 2 && x (-8) 12).toNat + (x (-9) 3 && x (-9) 13).toNat + (x (-10) 4 && x (-10) 14).toNat + (x (-11) 5).toNat := by have q := hcov10 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20369 : 1 ≤ (x 4 11).toNat + (x 3 1 && x 3 12).toNat + (x 2 2 && x 2 13).toNat + (x 1 3 && x 1 14).toNat + (x 0 4).toNat := by have q := hcov11 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20370 : 1 ≤ (x (-9) 13).toNat + (x (-10) 1 && x (-10) 14).toNat + (x (-11) 2).toNat := by have q := hcov13 (-9); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20371 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have r20372 : (x (-11) 2).toNat ≤ (x (-11) 14).toNat := himp _ _ (hp2 (-11))
              have r20373 : (x (-9) 13).toNat ≤ (x (-9) 1).toNat := himp _ _ (hp13 (-9))
              have r20374 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
              have r20375 : (x 5 10).toNat ≤ (x 5 2).toNat := himp _ _ (hp10 5)
              have r20376 : (x 6 6).toNat ≤ (x 6 14).toNat := himp _ _ (hp6 6)
              have r20377 := hand2 (x 11 1) (x 11 4)
              have r20378 := hand2 (x 10 2) (x 10 5)
              have r20379 := hand2 (x 9 3) (x 9 6)
              have r20380 := hand2 (x 8 4) (x 8 7)
              have r20381 := hand2 (x 7 5) (x 7 8)
              have r20382 := hand1 (x 6 6) (x 6 9)
              have r20383 := hand2 (x 6 6) (x 6 9)
              have r20384 := hand2 (x 5 7) (x 5 10)
              have r20385 := hand1 (x (-6) 8) (x (-6) 12)
              have r20386 := hand1 (x (-7) 9) (x (-7) 13)
              have r20387 := hand2 (x (-7) 1) (x (-7) 10)
              have r20388 := hand2 (x (-8) 2) (x (-8) 11)
              have r20389 := hand2 (x (-9) 3) (x (-9) 12)
              have r20390 := hand1 (x (-10) 4) (x (-10) 13)
              have r20391 := hand1 (x (-11) 5) (x (-11) 14)
              have r20392 := hand2 (x 5 1) (x 5 10)
              have r20393 := hand2 (x 4 2) (x 4 11)
              have r20394 := hand2 (x (-7) 1) (x (-7) 11)
              have r20395 := hand2 (x (-8) 2) (x (-8) 12)
              have r20396 := hand1 (x (-9) 3) (x (-9) 13)
              have r20397 := hand2 (x (-9) 3) (x (-9) 13)
              have r20398 := hand1 (x (-10) 4) (x (-10) 14)
              have r20399 := hand1 (x 2 2) (x 2 13)
              have r20400 := hand2 (x (-10) 1) (x (-10) 14)
              have r20401 := hand1 (x 4 1) (x 4 14)
              linarith only [r20335, r20336, r20337, r20338, r20339, e20340, e20341, e20342, e20343, e20344, e20345, r20346, e20347, e20348, e20349, e20350, e20351, e20352, r20353, e20354, e20355, r20356, e20357, e20358, r20359, r20360, r20361, r20362, r20363, e20364, e20365, r20366, r20367, r20368, r20369, r20370, r20371, r20372, r20373, r20374, r20375, r20376, r20377, r20378, r20379, r20380, r20381, r20382, r20383, r20384, r20385, r20386, r20387, r20388, r20389, r20390, r20391, r20392, r20393, r20394, r20395, r20396, r20397, r20398, r20399, r20400, r20401, d20309, d20293, d19113, g2, d19097, f20260, g5, f20330, g7, g8, g10, g14, g17, f19688, g19, g23, g24, d19579, g25, g26, g29, d19033, g34, d19073, d19093, g35, d20331, d19623, d19643, d19663, d19683, g53, d19583, g54, g65, d19689]
            · have f20521 : (x (-1) 7).toNat = 1 := by rw [h20329]; rfl
              have d20522 : (x 6 8).toNat = 0 := by
                have r20523 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20524 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e20525 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e20526 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e20527 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e20528 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e20529 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b20530 := hb (x (-1) 7)
                have b20531 := hb (x 0 6)
                have b20532 := hb (x 1 5)
                have b20533 := hb (x 2 4)
                have b20534 := hb (x 3 11)
                have b20535 := hb (x 4 10)
                have b20536 := hb (x 5 9)
                have b20537 := hb (x 6 8)
                clear * - r20523 e20524 e20525 e20526 e20527 e20528 e20529 b20530 b20531 b20532 b20533 b20534 b20535 b20536 b20537 d19579 g19 g10 f20521
                omega
              have d20538 : (x 5 9).toNat = 0 := by
                have r20539 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20540 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
                have e20541 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
                have e20542 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
                have e20543 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
                have e20544 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
                have e20545 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
                have b20546 := hb (x (-1) 7)
                have b20547 := hb (x 0 6)
                have b20548 := hb (x 1 5)
                have b20549 := hb (x 2 4)
                have b20550 := hb (x 3 11)
                have b20551 := hb (x 4 10)
                have b20552 := hb (x 5 9)
                have b20553 := hb (x 6 8)
                clear * - r20539 e20540 e20541 e20542 e20543 e20544 e20545 b20546 b20547 b20548 b20549 b20550 b20551 b20552 b20553 d20522 d19579 g19 g10 f20521
                omega
              have d20554 : (x 4 1 && x 4 10).toNat = 1 := by
                have r20555 : 1 ≤ (x 5 9).toNat + (x 4 1 && x 4 10).toNat + (x 3 2 && x 3 11).toNat + (x 2 3 && x 2 12).toNat + (x 1 4 && x 1 13).toNat + (x 0 5 && x 0 14).toNat + (x (-1) 6).toNat := by have q := hcov9 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have b20556 := hb (x (-1) 6)
                have b20557 := hb (x 5 9)
                have b20558 := hb (x 4 1 && x 4 10)
                have b20559 := hb (x 3 2 && x 3 11)
                have b20560 := hb (x 2 3 && x 2 12)
                have b20561 := hb (x 1 4 && x 1 13)
                have b20562 := hb (x 0 5 && x 0 14)
                clear * - r20555 b20556 b20557 b20558 b20559 b20560 b20561 b20562 d20538 g50 d19571 g51 g52 f20326
                omega
              have d20563 : (x 4 10).toNat = 1 := by
                have r20564 := hand2 (x 4 1) (x 4 10)
                have b20565 := hb (x 4 10)
                have b20566 := hb (x 4 1 && x 4 10)
                clear * - r20564 b20565 b20566 d20554
                omega
              have d20567 : (x 4 2).toNat = 1 := by
                have r20568 : (x 4 10).toNat ≤ (x 4 2).toNat := himp _ _ (hp10 4)
                have b20569 := hb (x 4 2)
                have b20570 := hb (x 4 10)
                clear * - r20568 b20569 b20570 d20563
                omega
              have d20571 : (x 6 12).toNat = 0 := by
                have r20572 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20573 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e20574 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b20575 := hb (x 3 3)
                have b20576 := hb (x 4 2)
                have b20577 := hb (x 5 13)
                have b20578 := hb (x 6 12)
                clear * - r20572 e20573 e20574 b20575 b20576 b20577 b20578 d20567
                omega
              have d20579 : (x 5 13).toNat = 0 := by
                have r20580 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20581 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e20582 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b20583 := hb (x 3 3)
                have b20584 := hb (x 4 2)
                have b20585 := hb (x 5 13)
                have b20586 := hb (x 6 12)
                clear * - r20580 e20581 e20582 b20583 b20584 b20585 b20586 d20571 d20567
                omega
              have d20587 : (x 3 3).toNat = 0 := by
                have r20588 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
                have e20589 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
                have e20590 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
                have b20591 := hb (x 3 3)
                have b20592 := hb (x 4 2)
                have b20593 := hb (x 5 13)
                have b20594 := hb (x 6 12)
                clear * - r20588 e20589 e20590 b20591 b20592 b20593 b20594 d20571 d20579 d20567
                omega
              have d20595 : (x 3 11).toNat = 0 := by
                have r20596 : (x 3 11).toNat ≤ (x 3 3).toNat := himp _ _ (hp11 3)
                have b20597 := hb (x 3 3)
                have b20598 := hb (x 3 11)
                clear * - r20596 b20597 b20598 d20587
                omega
              have r20599 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20600 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
              have e20601 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
              have e20602 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
              have e20603 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
              have e20604 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
              have e20605 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
              have b20606 := hb (x (-1) 7)
              have b20607 := hb (x 0 6)
              have b20608 := hb (x 1 5)
              have b20609 := hb (x 2 4)
              have b20610 := hb (x 3 11)
              have b20611 := hb (x 4 10)
              have b20612 := hb (x 5 9)
              have b20613 := hb (x 6 8)
              linarith only [r20599, e20600, e20601, e20602, e20603, e20604, e20605, b20606, b20607, b20608, b20609, b20610, b20611, b20612, b20613, d20522, d20538, d20563, d20595, d19579, g19, g10, f20521]
          · have f20614 : (x 1 6).toNat = 1 := by rw [h20327]; rfl
            have d20615 : (x 7 8).toNat = 0 := by
              have r20616 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20617 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
              have e20618 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
              have e20619 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
              have e20620 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
              have e20621 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
              have e20622 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
              have b20623 := hb (x 0 7)
              have b20624 := hb (x 1 6)
              have b20625 := hb (x 2 5)
              have b20626 := hb (x 3 4)
              have b20627 := hb (x 4 11)
              have b20628 := hb (x 5 10)
              have b20629 := hb (x 6 9)
              have b20630 := hb (x 7 8)
              clear * - r20616 e20617 e20618 e20619 e20620 e20621 e20622 b20623 b20624 b20625 b20626 b20627 b20628 b20629 b20630 g27 f20614 g11
              omega
            have d20631 : (x 6 9).toNat = 0 := by
              have r20632 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20633 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
              have e20634 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
              have e20635 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
              have e20636 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
              have e20637 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
              have e20638 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
              have b20639 := hb (x 0 7)
              have b20640 := hb (x 1 6)
              have b20641 := hb (x 2 5)
              have b20642 := hb (x 3 4)
              have b20643 := hb (x 4 11)
              have b20644 := hb (x 5 10)
              have b20645 := hb (x 6 9)
              have b20646 := hb (x 7 8)
              clear * - r20632 e20633 e20634 e20635 e20636 e20637 e20638 b20639 b20640 b20641 b20642 b20643 b20644 b20645 b20646 d20615 g27 f20614 g11
              omega
            have d20647 : (x 5 10).toNat = 0 := by
              have r20648 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have e20649 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
              have e20650 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
              have e20651 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
              have e20652 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
              have e20653 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
              have e20654 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
              have b20655 := hb (x 0 7)
              have b20656 := hb (x 1 6)
              have b20657 := hb (x 2 5)
              have b20658 := hb (x 3 4)
              have b20659 := hb (x 4 11)
              have b20660 := hb (x 5 10)
              have b20661 := hb (x 6 9)
              have b20662 := hb (x 7 8)
              clear * - r20648 e20649 e20650 e20651 e20652 e20653 e20654 b20655 b20656 b20657 b20658 b20659 b20660 b20661 b20662 d20615 d20631 g27 f20614 g11
              omega
            have d20663 : (x 5 1 && x 5 10).toNat = 0 := by
              have r20664 := hand2 (x 5 1) (x 5 10)
              have b20665 := hb (x 5 10)
              have b20666 := hb (x 5 1 && x 5 10)
              clear * - r20664 b20665 b20666 d20647
              omega
            have d20667 : (x 4 2 && x 4 11).toNat = 1 := by
              have r20668 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
              have b20669 := hb (x 0 6)
              have b20670 := hb (x 6 9)
              have b20671 := hb (x 5 1 && x 5 10)
              have b20672 := hb (x 4 2 && x 4 11)
              have b20673 := hb (x 3 3 && x 3 12)
              have b20674 := hb (x 2 4 && x 2 13)
              have b20675 := hb (x 1 5 && x 1 14)
              clear * - r20668 b20669 b20670 b20671 b20672 b20673 b20674 b20675 d20631 d20663 g53 d19583 g54 g10
              omega
            have d20676 : (x 4 11).toNat = 1 := by
              have r20677 := hand2 (x 4 2) (x 4 11)
              have b20678 := hb (x 4 11)
              have b20679 := hb (x 4 2 && x 4 11)
              clear * - r20677 b20678 b20679 d20667
              omega
            have r20680 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20681 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
            have e20682 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
            have e20683 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
            have e20684 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
            have e20685 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
            have e20686 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
            have b20687 := hb (x 0 7)
            have b20688 := hb (x 1 6)
            have b20689 := hb (x 2 5)
            have b20690 := hb (x 3 4)
            have b20691 := hb (x 4 11)
            have b20692 := hb (x 5 10)
            have b20693 := hb (x 6 9)
            have b20694 := hb (x 7 8)
            linarith only [r20680, e20681, e20682, e20683, e20684, e20685, e20686, b20687, b20688, b20689, b20690, b20691, b20692, b20693, b20694, d20615, d20631, d20647, d20676, g27, f20614, g11]
        · have f20695 : (x (-1) 6).toNat = 1 := by rw [h20325]; rfl
          have d20696 : (x 5 8).toNat = 0 := by
            have r20697 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20698 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
            have e20699 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
            have e20700 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
            have e20701 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
            have e20702 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
            have e20703 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
            have b20704 := hb (x (-2) 7)
            have b20705 := hb (x (-1) 6)
            have b20706 := hb (x 0 5)
            have b20707 := hb (x 1 4)
            have b20708 := hb (x 2 11)
            have b20709 := hb (x 3 10)
            have b20710 := hb (x 4 9)
            have b20711 := hb (x 5 8)
            clear * - r20697 e20698 e20699 e20700 e20701 e20702 e20703 b20704 b20705 b20706 b20707 b20708 b20709 b20710 b20711 g28 g18 g9 f20695
            omega
          have d20712 : (x 5 8 && x 5 10).toNat = 0 := by
            have r20713 := hand1 (x 5 8) (x 5 10)
            have b20714 := hb (x 5 8)
            have b20715 := hb (x 5 8 && x 5 10)
            clear * - r20713 b20714 b20715 d20696
            omega
          have d20716 : (x 4 9).toNat = 0 := by
            have r20717 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20718 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
            have e20719 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
            have e20720 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
            have e20721 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
            have e20722 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
            have e20723 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
            have b20724 := hb (x (-2) 7)
            have b20725 := hb (x (-1) 6)
            have b20726 := hb (x 0 5)
            have b20727 := hb (x 1 4)
            have b20728 := hb (x 2 11)
            have b20729 := hb (x 3 10)
            have b20730 := hb (x 4 9)
            have b20731 := hb (x 5 8)
            clear * - r20717 e20718 e20719 e20720 e20721 e20722 e20723 b20724 b20725 b20726 b20727 b20728 b20729 b20730 b20731 d20696 g28 g18 g9 f20695
            omega
          have d20732 : (x 4 9 && x 4 11).toNat = 0 := by
            have r20733 := hand1 (x 4 9) (x 4 11)
            have b20734 := hb (x 4 9)
            have b20735 := hb (x 4 9 && x 4 11)
            clear * - r20733 b20734 b20735 d20716
            omega
          have d20736 : (x 2 11).toNat = 0 := by
            have r20737 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20738 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
            have e20739 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
            have e20740 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
            have e20741 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
            have e20742 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
            have e20743 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
            have b20744 := hb (x (-2) 7)
            have b20745 := hb (x (-1) 6)
            have b20746 := hb (x 0 5)
            have b20747 := hb (x 1 4)
            have b20748 := hb (x 2 11)
            have b20749 := hb (x 3 10)
            have b20750 := hb (x 4 9)
            have b20751 := hb (x 5 8)
            clear * - r20737 e20738 e20739 e20740 e20741 e20742 e20743 b20744 b20745 b20746 b20747 b20748 b20749 b20750 b20751 d20696 d20716 g28 g18 g9 f20695
            omega
          have d20752 : (x 2 11 && x 2 13).toNat = 0 := by
            have r20753 := hand1 (x 2 11) (x 2 13)
            have b20754 := hb (x 2 11)
            have b20755 := hb (x 2 11 && x 2 13)
            clear * - r20753 b20754 b20755 d20736
            omega
          have d20756 : (x (-2) 7).toNat = 0 := by
            have r20757 : (x 5 8).toNat + (x 4 1 && x 4 9).toNat + (x 3 2 && x 3 10).toNat + (x 2 3 && x 2 11).toNat + (x 1 4 && x 1 12).toNat + (x 0 5 && x 0 13).toNat + (x (-1) 6 && x (-1) 14).toNat + (x (-2) 7).toNat = 1 := by have q := hd8 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
            have e20758 : (x 4 1 && x 4 9).toNat = (x 4 9).toNat := handr _ _ (fun h => hp9 4 (h))
            have e20759 : (x 3 2 && x 3 10).toNat = (x 3 10).toNat := handr _ _ (fun h => hp10 3 (h))
            have e20760 : (x 2 3 && x 2 11).toNat = (x 2 11).toNat := handr _ _ (fun h => hp11 2 (h))
            have e20761 : (x 1 4 && x 1 12).toNat = (x 1 4).toNat := handl _ _ (fun h => hp4 1 (h))
            have e20762 : (x 0 5 && x 0 13).toNat = (x 0 5).toNat := handl _ _ (fun h => hp5 0 (h))
            have e20763 : (x (-1) 6 && x (-1) 14).toNat = (x (-1) 6).toNat := handl _ _ (fun h => hp6 (-1) (h))
            have b20764 := hb (x (-2) 7)
            have b20765 := hb (x (-1) 6)
            have b20766 := hb (x 0 5)
            have b20767 := hb (x 1 4)
            have b20768 := hb (x 2 11)
            have b20769 := hb (x 3 10)
            have b20770 := hb (x 4 9)
            have b20771 := hb (x 5 8)
            clear * - r20757 e20758 e20759 e20760 e20761 e20762 e20763 b20764 b20765 b20766 b20767 b20768 b20769 b20770 b20771 d20696 d20716 g28 d20736 g18 g9 f20695
            omega
          have r20772 : (x 4 1).toNat + (x 3 2).toNat + (x 2 3).toNat + (x 1 4).toNat + (x 0 5).toNat + (x (-1) 6).toNat + (x (-2) 7).toNat + (x (-3) 8).toNat + (x (-4) 9).toNat + (x (-5) 10).toNat + (x (-6) 11).toNat + (x (-7) 12).toNat + (x (-8) 13).toNat + (x (-9) 14).toNat = 3 := by have q := hcount 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r20773 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r20774 : (x (-6) 8).toNat + (x (-7) 1 && x (-7) 9).toNat + (x (-8) 2 && x (-8) 10).toNat + (x (-9) 3 && x (-9) 11).toNat + (x (-10) 4 && x (-10) 12).toNat + (x (-11) 5 && x (-11) 13).toNat + (x (-12) 6 && x (-12) 14).toNat + (x (-13) 7).toNat = 1 := by have q := hd8 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20775 : (x (-7) 1 && x (-7) 9).toNat = (x (-7) 9).toNat := handr _ _ (fun h => hp9 (-7) (h))
          have e20776 : (x (-8) 2 && x (-8) 10).toNat = (x (-8) 10).toNat := handr _ _ (fun h => hp10 (-8) (h))
          have e20777 : (x (-9) 3 && x (-9) 11).toNat = (x (-9) 11).toNat := handr _ _ (fun h => hp11 (-9) (h))
          have e20778 : (x (-10) 4 && x (-10) 12).toNat = (x (-10) 4).toNat := handl _ _ (fun h => hp4 (-10) (h))
          have e20779 : (x (-11) 5 && x (-11) 13).toNat = (x (-11) 5).toNat := handl _ _ (fun h => hp5 (-11) (h))
          have e20780 : (x (-12) 6 && x (-12) 14).toNat = (x (-12) 6).toNat := handl _ _ (fun h => hp6 (-12) (h))
          have r20781 : (x 6 8).toNat + (x 5 1 && x 5 9).toNat + (x 4 2 && x 4 10).toNat + (x 3 3 && x 3 11).toNat + (x 2 4 && x 2 12).toNat + (x 1 5 && x 1 13).toNat + (x 0 6 && x 0 14).toNat + (x (-1) 7).toNat = 1 := by have q := hd8 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20782 : (x 5 1 && x 5 9).toNat = (x 5 9).toNat := handr _ _ (fun h => hp9 5 (h))
          have e20783 : (x 4 2 && x 4 10).toNat = (x 4 10).toNat := handr _ _ (fun h => hp10 4 (h))
          have e20784 : (x 3 3 && x 3 11).toNat = (x 3 11).toNat := handr _ _ (fun h => hp11 3 (h))
          have e20785 : (x 2 4 && x 2 12).toNat = (x 2 4).toNat := handl _ _ (fun h => hp4 2 (h))
          have e20786 : (x 1 5 && x 1 13).toNat = (x 1 5).toNat := handl _ _ (fun h => hp5 1 (h))
          have e20787 : (x 0 6 && x 0 14).toNat = (x 0 6).toNat := handl _ _ (fun h => hp6 0 (h))
          have r20788 : (x 6 12).toNat + (x 5 1 && x 5 13).toNat + (x 4 2 && x 4 14).toNat + (x 3 3).toNat = 1 := by have q := hd12 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20789 : (x 5 1 && x 5 13).toNat = (x 5 13).toNat := handr _ _ (fun h => hp13 5 (h))
          have e20790 : (x 4 2 && x 4 14).toNat = (x 4 2).toNat := handl _ _ (fun h => hp2 4 (h))
          have r20791 : 1 ≤ (x 14 1).toNat + (x 13 1 && x 13 2).toNat + (x 12 2 && x 12 3).toNat + (x 11 3 && x 11 4).toNat + (x 10 4 && x 10 5).toNat + (x 9 5 && x 9 6).toNat + (x 8 6 && x 8 7).toNat + (x 7 7 && x 7 8).toNat + (x 6 8 && x 6 9).toNat + (x 5 9 && x 5 10).toNat + (x 4 10 && x 4 11).toNat + (x 3 11 && x 3 12).toNat + (x 2 12 && x 2 13).toNat + (x 1 13 && x 1 14).toNat + (x 0 14).toNat := by have q := hcov1 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r20792 : 1 ≤ (x 13 2).toNat + (x 12 1 && x 12 3).toNat + (x 11 2 && x 11 4).toNat + (x 10 3 && x 10 5).toNat + (x 9 4 && x 9 6).toNat + (x 8 5 && x 8 7).toNat + (x 7 6 && x 7 8).toNat + (x 6 7 && x 6 9).toNat + (x 5 8 && x 5 10).toNat + (x 4 9 && x 4 11).toNat + (x 3 10 && x 3 12).toNat + (x 2 11 && x 2 13).toNat + (x 1 12 && x 1 14).toNat + (x 0 13).toNat := by have q := hcov2 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r20793 : 1 ≤ (x 2 4).toNat + (x 1 1 && x 1 5).toNat + (x 0 2 && x 0 6).toNat + (x (-1) 3 && x (-1) 7).toNat + (x (-2) 4 && x (-2) 8).toNat + (x (-3) 5 && x (-3) 9).toNat + (x (-4) 6 && x (-4) 10).toNat + (x (-5) 7 && x (-5) 11).toNat + (x (-6) 8 && x (-6) 12).toNat + (x (-7) 9 && x (-7) 13).toNat + (x (-8) 10 && x (-8) 14).toNat + (x (-9) 11).toNat := by have q := hcov4 2; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have e20794 : (x 1 1 && x 1 5).toNat = (x 1 5).toNat := handr _ _ (fun h => hp13 1 (hp5 1 (h)))
          have e20795 : (x (-8) 10 && x (-8) 14).toNat = (x (-8) 10).toNat := handl _ _ (fun h => hp2 (-8) (hp10 (-8) (h)))
          have r20796 : 1 ≤ (x 10 5).toNat + (x 9 1 && x 9 6).toNat + (x 8 2 && x 8 7).toNat + (x 7 3 && x 7 8).toNat + (x 6 4 && x 6 9).toNat + (x 5 5 && x 5 10).toNat + (x 4 6 && x 4 11).toNat + (x 3 7 && x 3 12).toNat + (x 2 8 && x 2 13).toNat + (x 1 9 && x 1 14).toNat + (x 0 10).toNat := by have q := hcov5 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r20797 : 1 ≤ (x 6 9).toNat + (x 5 1 && x 5 10).toNat + (x 4 2 && x 4 11).toNat + (x 3 3 && x 3 12).toNat + (x 2 4 && x 2 13).toNat + (x 1 5 && x 1 14).toNat + (x 0 6).toNat := by have q := hcov9 6; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r20798 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r20799 : 1 ≤ (x (-6) 11).toNat + (x (-7) 1 && x (-7) 12).toNat + (x (-8) 2 && x (-8) 13).toNat + (x (-9) 3 && x (-9) 14).toNat + (x (-10) 4).toNat := by have q := hcov11 (-6); simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r20800 : 1 ≤ (x 5 13).toNat + (x 4 1 && x 4 14).toNat + (x 3 2).toNat := by have q := hcov13 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
          have r20801 : (x 6 4).toNat ≤ (x 6 12).toNat := himp _ _ (hp4 6)
          have r20802 := hand2 (x 13 1) (x 13 2)
          have r20803 := hand2 (x 12 2) (x 12 3)
          have r20804 := hand2 (x 11 3) (x 11 4)
          have r20805 := hand2 (x 10 4) (x 10 5)
          have r20806 := hand2 (x 9 5) (x 9 6)
          have r20807 := hand2 (x 8 6) (x 8 7)
          have r20808 := hand2 (x 7 7) (x 7 8)
          have r20809 := hand1 (x 6 8) (x 6 9)
          have r20810 := hand1 (x 5 9) (x 5 10)
          have r20811 := hand1 (x 4 10) (x 4 11)
          have r20812 := hand2 (x 12 1) (x 12 3)
          have r20813 := hand2 (x 11 2) (x 11 4)
          have r20814 := hand2 (x 10 3) (x 10 5)
          have r20815 := hand2 (x 9 4) (x 9 6)
          have r20816 := hand2 (x 8 5) (x 8 7)
          have r20817 := hand2 (x 7 6) (x 7 8)
          have r20818 := hand2 (x 6 7) (x 6 9)
          have r20819 := hand2 (x (-1) 3) (x (-1) 7)
          have r20820 := hand1 (x (-6) 8) (x (-6) 12)
          have r20821 := hand1 (x (-7) 9) (x (-7) 13)
          have r20822 := hand2 (x 9 1) (x 9 6)
          have r20823 := hand2 (x 8 2) (x 8 7)
          have r20824 := hand2 (x 7 3) (x 7 8)
          have r20825 := hand1 (x 6 4) (x 6 9)
          have r20826 := hand2 (x 5 5) (x 5 10)
          have r20827 := hand2 (x 4 6) (x 4 11)
          have r20828 := hand2 (x 5 1) (x 5 10)
          have r20829 := hand2 (x 4 2) (x 4 11)
          have r20830 := hand2 (x 4 1) (x 4 11)
          have r20831 := hand1 (x 2 3) (x 2 13)
          have r20832 := hand2 (x (-7) 1) (x (-7) 12)
          have r20833 := hand2 (x (-8) 2) (x (-8) 13)
          have r20834 := hand2 (x (-9) 3) (x (-9) 14)
          have r20835 := hand1 (x 4 1) (x 4 14)
          linarith only [r20772, r20773, r20774, e20775, e20776, e20777, e20778, e20779, e20780, r20781, e20782, e20783, e20784, e20785, e20786, e20787, r20788, e20789, e20790, r20791, r20792, r20793, e20794, e20795, r20796, r20797, r20798, r20799, r20800, r20801, r20802, r20803, r20804, r20805, r20806, r20807, r20808, r20809, r20810, r20811, r20812, r20813, r20814, r20815, r20816, r20817, r20818, r20819, r20820, r20821, r20822, r20823, r20824, r20825, r20826, r20827, r20828, r20829, r20830, r20831, r20832, r20833, r20834, r20835, d20756, f20695, g9, g10, g12, g15, g16, g18, g19, g23, d19579, g25, g26, g29, g30, d19575, g31, d20712, d20732, g32, d20752, g33, g35, d19623, d19643, d19663, d19683, g43, d19603, g44, g53, d19583, g54, g58, g59]
    · have f20943 : (x 1 3).toNat = 1 := by rw [h19687]; rfl
      have d20944 : (x 4 12).toNat = 0 := by
        have r20945 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e20946 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e20947 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b20948 := hb (x 1 3)
        have b20949 := hb (x 2 2)
        have b20950 := hb (x 3 13)
        have b20951 := hb (x 4 12)
        clear * - r20945 e20946 e20947 b20948 b20949 b20950 b20951 f20943
        omega
      have d20952 : (x 4 1 && x 4 12).toNat = 0 := by
        have r20953 := hand2 (x 4 1) (x 4 12)
        have b20954 := hb (x 4 12)
        have b20955 := hb (x 4 1 && x 4 12)
        clear * - r20953 b20954 b20955 d20944
        omega
      have d20956 : (x 4 4).toNat = 0 := by
        have r20957 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
        have b20958 := hb (x 4 4)
        have b20959 := hb (x 4 12)
        clear * - r20957 b20958 b20959 d20944
        omega
      have d20960 : (x 3 13).toNat = 0 := by
        have r20961 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e20962 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e20963 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b20964 := hb (x 1 3)
        have b20965 := hb (x 2 2)
        have b20966 := hb (x 3 13)
        have b20967 := hb (x 4 12)
        clear * - r20961 e20962 e20963 b20964 b20965 b20966 b20967 d20944 f20943
        omega
      have d20968 : (x 2 2).toNat = 0 := by
        have r20969 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e20970 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
        have e20971 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
        have b20972 := hb (x 1 3)
        have b20973 := hb (x 2 2)
        have b20974 := hb (x 3 13)
        have b20975 := hb (x 4 12)
        clear * - r20969 e20970 e20971 b20972 b20973 b20974 b20975 d20944 d20960 f20943
        omega
      have d20976 : (x 4 13).toNat = 1 := by
        have r20977 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b20978 := hb (x 2 2)
        have b20979 := hb (x 4 13)
        have b20980 := hb (x 3 1 && x 3 14)
        clear * - r20977 b20978 b20979 b20980 g68 d20968
        omega
      have d20981 : (x 4 1).toNat = 1 := by
        have r20982 : (x 4 13).toNat ≤ (x 4 1).toNat := himp _ _ (hp13 4)
        have b20983 := hb (x 4 1)
        have b20984 := hb (x 4 13)
        clear * - r20982 b20983 b20984 d20976
        omega
      have d20985 : (x 5 14).toNat = 0 := by
        have r20986 : (x 5 14).toNat + (x 4 1).toNat = 1 := by have q := hd14 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b20987 := hb (x 4 1)
        have b20988 := hb (x 5 14)
        clear * - r20986 b20987 b20988 d20981
        omega
      have d20989 : (x 5 3 && x 5 14).toNat = 0 := by
        have r20990 := hand2 (x 5 3) (x 5 14)
        have b20991 := hb (x 5 14)
        have b20992 := hb (x 5 3 && x 5 14)
        clear * - r20990 b20991 b20992 d20985
        omega
      have d20993 : (x 5 2).toNat = 0 := by
        have r20994 : (x 5 2).toNat ≤ (x 5 14).toNat := himp _ _ (hp2 5)
        have b20995 := hb (x 5 2)
        have b20996 := hb (x 5 14)
        clear * - r20994 b20995 b20996 d20985
        omega
      have d20997 : (x 5 12).toNat = 0 := by
        have r20998 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e20999 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e21000 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b21001 := hb (x 2 3)
        have b21002 := hb (x 3 2)
        have b21003 := hb (x 4 13)
        have b21004 := hb (x 5 12)
        clear * - r20998 e20999 e21000 b21001 b21002 b21003 b21004 d20976 g26
        omega
      have d21005 : (x 5 4).toNat = 0 := by
        have r21006 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
        have b21007 := hb (x 5 4)
        have b21008 := hb (x 5 12)
        clear * - r21006 b21007 b21008 d20997
        omega
      have d21009 : (x 2 3).toNat = 0 := by
        have r21010 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21011 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
        have e21012 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
        have b21013 := hb (x 2 3)
        have b21014 := hb (x 3 2)
        have b21015 := hb (x 4 13)
        have b21016 := hb (x 5 12)
        clear * - r21010 e21011 e21012 b21013 b21014 b21015 b21016 d20997 d20976 g26
        omega
      have d21017 : (x 2 3 && x 2 14).toNat = 0 := by
        have r21018 := hand1 (x 2 3) (x 2 14)
        have b21019 := hb (x 2 3)
        have b21020 := hb (x 2 3 && x 2 14)
        clear * - r21018 b21019 b21020 d21009
        omega
      have d21021 : (x 5 11).toNat = 1 := by
        have r21022 : 1 ≤ (x 5 11).toNat + (x 4 1 && x 4 12).toNat + (x 3 2 && x 3 13).toNat + (x 2 3 && x 2 14).toNat + (x 1 4).toNat := by have q := hcov11 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21023 := hb (x 1 4)
        have b21024 := hb (x 5 11)
        have b21025 := hb (x 4 1 && x 4 12)
        have b21026 := hb (x 3 2 && x 3 13)
        have b21027 := hb (x 2 3 && x 2 14)
        clear * - r21022 b21023 b21024 b21025 b21026 b21027 d20952 g66 d21017 g18
        omega
      have d21028 : (x 5 3).toNat = 1 := by
        have r21029 : (x 5 11).toNat ≤ (x 5 3).toNat := himp _ _ (hp11 5)
        have b21030 := hb (x 5 3)
        have b21031 := hb (x 5 11)
        clear * - r21029 b21030 b21031 d21021
        omega
      have d21032 : (x 8 12).toNat = 0 := by
        have r21033 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21034 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e21035 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b21036 := hb (x 5 3)
        have b21037 := hb (x 6 2)
        have b21038 := hb (x 7 13)
        have b21039 := hb (x 8 12)
        clear * - r21033 e21034 e21035 b21036 b21037 b21038 b21039 d21028
        omega
      have d21040 : (x 8 1 && x 8 12).toNat = 0 := by
        have r21041 := hand2 (x 8 1) (x 8 12)
        have b21042 := hb (x 8 12)
        have b21043 := hb (x 8 1 && x 8 12)
        clear * - r21041 b21042 b21043 d21032
        omega
      have d21044 : (x 8 4).toNat = 0 := by
        have r21045 : (x 8 4).toNat ≤ (x 8 12).toNat := himp _ _ (hp4 8)
        have b21046 := hb (x 8 4)
        have b21047 := hb (x 8 12)
        clear * - r21045 b21046 b21047 d21032
        omega
      have d21048 : (x 7 13).toNat = 0 := by
        have r21049 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21050 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e21051 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b21052 := hb (x 5 3)
        have b21053 := hb (x 6 2)
        have b21054 := hb (x 7 13)
        have b21055 := hb (x 8 12)
        clear * - r21049 e21050 e21051 b21052 b21053 b21054 b21055 d21032 d21028
        omega
      have d21056 : (x 7 2 && x 7 13).toNat = 0 := by
        have r21057 := hand2 (x 7 2) (x 7 13)
        have b21058 := hb (x 7 13)
        have b21059 := hb (x 7 2 && x 7 13)
        clear * - r21057 b21058 b21059 d21048
        omega
      have d21060 : (x 6 1 && x 6 14).toNat = 1 := by
        have r21061 : 1 ≤ (x 7 13).toNat + (x 6 1 && x 6 14).toNat + (x 5 2).toNat := by have q := hcov13 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21062 := hb (x 5 2)
        have b21063 := hb (x 7 13)
        have b21064 := hb (x 6 1 && x 6 14)
        clear * - r21061 b21062 b21063 b21064 d21048 d20993
        omega
      have d21065 : (x 6 1).toNat = 1 := by
        have r21066 := hand1 (x 6 1) (x 6 14)
        have b21067 := hb (x 6 1)
        have b21068 := hb (x 6 1 && x 6 14)
        clear * - r21066 b21067 b21068 d21060
        omega
      have d21069 : (x 7 14).toNat = 0 := by
        have r21070 : (x 7 14).toNat + (x 6 1).toNat = 1 := by have q := hd14 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21071 := hb (x 6 1)
        have b21072 := hb (x 7 14)
        clear * - r21070 b21071 b21072 d21065
        omega
      have d21073 : (x 7 1 && x 7 14).toNat = 0 := by
        have r21074 := hand2 (x 7 1) (x 7 14)
        have b21075 := hb (x 7 14)
        have b21076 := hb (x 7 1 && x 7 14)
        clear * - r21074 b21075 b21076 d21069
        omega
      have d21077 : (x 7 2).toNat = 0 := by
        have r21078 : (x 7 2).toNat ≤ (x 7 14).toNat := himp _ _ (hp2 7)
        have b21079 := hb (x 7 2)
        have b21080 := hb (x 7 14)
        clear * - r21078 b21079 b21080 d21069
        omega
      have d21081 : (x 6 2).toNat = 0 := by
        have r21082 : (x 8 12).toNat + (x 7 1 && x 7 13).toNat + (x 6 2 && x 6 14).toNat + (x 5 3).toNat = 1 := by have q := hd12 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21083 : (x 7 1 && x 7 13).toNat = (x 7 13).toNat := handr _ _ (fun h => hp13 7 (h))
        have e21084 : (x 6 2 && x 6 14).toNat = (x 6 2).toNat := handl _ _ (fun h => hp2 6 (h))
        have b21085 := hb (x 5 3)
        have b21086 := hb (x 6 2)
        have b21087 := hb (x 7 13)
        have b21088 := hb (x 8 12)
        clear * - r21082 e21083 e21084 b21085 b21086 b21087 b21088 d21032 d21048 d21028
        omega
      have d21089 : (x 6 2 && x 6 13).toNat = 0 := by
        have r21090 := hand1 (x 6 2) (x 6 13)
        have b21091 := hb (x 6 2)
        have b21092 := hb (x 6 2 && x 6 13)
        clear * - r21090 b21091 b21092 d21081
        omega
      have d21093 : (x 8 13).toNat = 1 := by
        have r21094 : 1 ≤ (x 8 13).toNat + (x 7 1 && x 7 14).toNat + (x 6 2).toNat := by have q := hcov13 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21095 := hb (x 6 2)
        have b21096 := hb (x 8 13)
        have b21097 := hb (x 7 1 && x 7 14)
        clear * - r21094 b21095 b21096 b21097 d21073 d21081
        omega
      have d21098 : (x 8 1).toNat = 1 := by
        have r21099 : (x 8 13).toNat ≤ (x 8 1).toNat := himp _ _ (hp13 8)
        have b21100 := hb (x 8 1)
        have b21101 := hb (x 8 13)
        clear * - r21099 b21100 b21101 d21093
        omega
      have d21102 : (x 9 14).toNat = 0 := by
        have r21103 : (x 9 14).toNat + (x 8 1).toNat = 1 := by have q := hd14 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21104 := hb (x 8 1)
        have b21105 := hb (x 9 14)
        clear * - r21103 b21104 b21105 d21098
        omega
      have d21106 : (x 9 3 && x 9 14).toNat = 0 := by
        have r21107 := hand2 (x 9 3) (x 9 14)
        have b21108 := hb (x 9 14)
        have b21109 := hb (x 9 3 && x 9 14)
        clear * - r21107 b21108 b21109 d21102
        omega
      have d21110 : (x 9 2).toNat = 0 := by
        have r21111 : (x 9 2).toNat ≤ (x 9 14).toNat := himp _ _ (hp2 9)
        have b21112 := hb (x 9 2)
        have b21113 := hb (x 9 14)
        clear * - r21111 b21112 b21113 d21102
        omega
      have d21114 : (x 9 12).toNat = 0 := by
        have r21115 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21116 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e21117 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b21118 := hb (x 6 3)
        have b21119 := hb (x 7 2)
        have b21120 := hb (x 8 13)
        have b21121 := hb (x 9 12)
        clear * - r21115 e21116 e21117 b21118 b21119 b21120 b21121 d21093 d21077
        omega
      have d21122 : (x 9 4).toNat = 0 := by
        have r21123 : (x 9 4).toNat ≤ (x 9 12).toNat := himp _ _ (hp4 9)
        have b21124 := hb (x 9 4)
        have b21125 := hb (x 9 12)
        clear * - r21123 b21124 b21125 d21114
        omega
      have d21126 : (x 6 3).toNat = 0 := by
        have r21127 : (x 9 12).toNat + (x 8 1 && x 8 13).toNat + (x 7 2 && x 7 14).toNat + (x 6 3).toNat = 1 := by have q := hd12 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21128 : (x 8 1 && x 8 13).toNat = (x 8 13).toNat := handr _ _ (fun h => hp13 8 (h))
        have e21129 : (x 7 2 && x 7 14).toNat = (x 7 2).toNat := handl _ _ (fun h => hp2 7 (h))
        have b21130 := hb (x 6 3)
        have b21131 := hb (x 7 2)
        have b21132 := hb (x 8 13)
        have b21133 := hb (x 9 12)
        clear * - r21127 e21128 e21129 b21130 b21131 b21132 b21133 d21114 d21093 d21077
        omega
      have d21134 : (x 6 3 && x 6 14).toNat = 0 := by
        have r21135 := hand1 (x 6 3) (x 6 14)
        have b21136 := hb (x 6 3)
        have b21137 := hb (x 6 3 && x 6 14)
        clear * - r21135 b21136 b21137 d21126
        omega
      have d21138 : (x 9 11).toNat = 1 := by
        have r21139 : 1 ≤ (x 9 11).toNat + (x 8 1 && x 8 12).toNat + (x 7 2 && x 7 13).toNat + (x 6 3 && x 6 14).toNat + (x 5 4).toNat := by have q := hcov11 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21140 := hb (x 5 4)
        have b21141 := hb (x 9 11)
        have b21142 := hb (x 8 1 && x 8 12)
        have b21143 := hb (x 7 2 && x 7 13)
        have b21144 := hb (x 6 3 && x 6 14)
        clear * - r21139 b21140 b21141 b21142 b21143 b21144 d21040 d21056 d21134 d21005
        omega
      have d21145 : (x 9 3).toNat = 1 := by
        have r21146 : (x 9 11).toNat ≤ (x 9 3).toNat := himp _ _ (hp11 9)
        have b21147 := hb (x 9 3)
        have b21148 := hb (x 9 11)
        clear * - r21146 b21147 b21148 d21138
        omega
      have d21149 : (x 12 12).toNat = 0 := by
        have r21150 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21151 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e21152 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b21153 := hb (x 9 3)
        have b21154 := hb (x 10 2)
        have b21155 := hb (x 11 13)
        have b21156 := hb (x 12 12)
        clear * - r21150 e21151 e21152 b21153 b21154 b21155 b21156 d21145
        omega
      have d21157 : (x 12 1 && x 12 12).toNat = 0 := by
        have r21158 := hand2 (x 12 1) (x 12 12)
        have b21159 := hb (x 12 12)
        have b21160 := hb (x 12 1 && x 12 12)
        clear * - r21158 b21159 b21160 d21149
        omega
      have d21161 : (x 12 4).toNat = 0 := by
        have r21162 : (x 12 4).toNat ≤ (x 12 12).toNat := himp _ _ (hp4 12)
        have b21163 := hb (x 12 4)
        have b21164 := hb (x 12 12)
        clear * - r21162 b21163 b21164 d21149
        omega
      have d21165 : (x 11 13).toNat = 0 := by
        have r21166 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21167 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e21168 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b21169 := hb (x 9 3)
        have b21170 := hb (x 10 2)
        have b21171 := hb (x 11 13)
        have b21172 := hb (x 12 12)
        clear * - r21166 e21167 e21168 b21169 b21170 b21171 b21172 d21149 d21145
        omega
      have d21173 : (x 11 2 && x 11 13).toNat = 0 := by
        have r21174 := hand2 (x 11 2) (x 11 13)
        have b21175 := hb (x 11 13)
        have b21176 := hb (x 11 2 && x 11 13)
        clear * - r21174 b21175 b21176 d21165
        omega
      have d21177 : (x 10 1 && x 10 14).toNat = 1 := by
        have r21178 : 1 ≤ (x 11 13).toNat + (x 10 1 && x 10 14).toNat + (x 9 2).toNat := by have q := hcov13 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21179 := hb (x 9 2)
        have b21180 := hb (x 11 13)
        have b21181 := hb (x 10 1 && x 10 14)
        clear * - r21178 b21179 b21180 b21181 d21165 d21110
        omega
      have d21182 : (x 10 14).toNat = 1 := by
        have r21183 := hand2 (x 10 1) (x 10 14)
        have b21184 := hb (x 10 14)
        have b21185 := hb (x 10 1 && x 10 14)
        clear * - r21183 b21184 b21185 d21177
        omega
      have d21186 : (x 9 1).toNat = 0 := by
        have r21187 : (x 10 14).toNat + (x 9 1).toNat = 1 := by have q := hd14 10; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21188 := hb (x 9 1)
        have b21189 := hb (x 10 14)
        clear * - r21187 b21188 b21189 d21182
        omega
      have d21190 : (x 9 13).toNat = 0 := by
        have r21191 : (x 9 13).toNat ≤ (x 9 1).toNat := himp _ _ (hp13 9)
        have b21192 := hb (x 9 1)
        have b21193 := hb (x 9 13)
        clear * - r21191 b21192 b21193 d21186
        omega
      have d21194 : (x 8 1 && x 8 14).toNat = 1 := by
        have r21195 : 1 ≤ (x 9 13).toNat + (x 8 1 && x 8 14).toNat + (x 7 2).toNat := by have q := hcov13 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21196 := hb (x 7 2)
        have b21197 := hb (x 9 13)
        have b21198 := hb (x 8 1 && x 8 14)
        clear * - r21195 b21196 b21197 b21198 d21190 d21077
        omega
      have d21199 : (x 8 14).toNat = 1 := by
        have r21200 := hand2 (x 8 1) (x 8 14)
        have b21201 := hb (x 8 14)
        have b21202 := hb (x 8 1 && x 8 14)
        clear * - r21200 b21201 b21202 d21194
        omega
      have d21203 : (x 7 1).toNat = 0 := by
        have r21204 : (x 8 14).toNat + (x 7 1).toNat = 1 := by have q := hd14 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21205 := hb (x 7 1)
        have b21206 := hb (x 8 14)
        clear * - r21204 b21205 b21206 d21199
        omega
      have d21207 : (x 7 1 && x 7 12).toNat = 0 := by
        have r21208 := hand1 (x 7 1) (x 7 12)
        have b21209 := hb (x 7 1)
        have b21210 := hb (x 7 1 && x 7 12)
        clear * - r21208 b21209 b21210 d21203
        omega
      have d21211 : (x 8 11).toNat = 1 := by
        have r21212 : 1 ≤ (x 8 11).toNat + (x 7 1 && x 7 12).toNat + (x 6 2 && x 6 13).toNat + (x 5 3 && x 5 14).toNat + (x 4 4).toNat := by have q := hcov11 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21213 := hb (x 4 4)
        have b21214 := hb (x 8 11)
        have b21215 := hb (x 7 1 && x 7 12)
        have b21216 := hb (x 6 2 && x 6 13)
        have b21217 := hb (x 5 3 && x 5 14)
        clear * - r21212 b21213 b21214 b21215 b21216 b21217 d21207 d21089 d20989 d20956
        omega
      have d21218 : (x 8 3).toNat = 1 := by
        have r21219 : (x 8 11).toNat ≤ (x 8 3).toNat := himp _ _ (hp11 8)
        have b21220 := hb (x 8 3)
        have b21221 := hb (x 8 11)
        clear * - r21219 b21220 b21221 d21211
        omega
      have d21222 : (x 11 12).toNat = 0 := by
        have r21223 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21224 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e21225 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b21226 := hb (x 8 3)
        have b21227 := hb (x 9 2)
        have b21228 := hb (x 10 13)
        have b21229 := hb (x 11 12)
        clear * - r21223 e21224 e21225 b21226 b21227 b21228 b21229 d21110 d21218
        omega
      have d21230 : (x 11 1 && x 11 12).toNat = 0 := by
        have r21231 := hand2 (x 11 1) (x 11 12)
        have b21232 := hb (x 11 12)
        have b21233 := hb (x 11 1 && x 11 12)
        clear * - r21231 b21232 b21233 d21222
        omega
      have d21234 : (x 10 13).toNat = 0 := by
        have r21235 : (x 11 12).toNat + (x 10 1 && x 10 13).toNat + (x 9 2 && x 9 14).toNat + (x 8 3).toNat = 1 := by have q := hd12 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21236 : (x 10 1 && x 10 13).toNat = (x 10 13).toNat := handr _ _ (fun h => hp13 10 (h))
        have e21237 : (x 9 2 && x 9 14).toNat = (x 9 2).toNat := handl _ _ (fun h => hp2 9 (h))
        have b21238 := hb (x 8 3)
        have b21239 := hb (x 9 2)
        have b21240 := hb (x 10 13)
        have b21241 := hb (x 11 12)
        clear * - r21235 e21236 e21237 b21238 b21239 b21240 b21241 d21222 d21110 d21218
        omega
      have d21242 : (x 10 2 && x 10 13).toNat = 0 := by
        have r21243 := hand2 (x 10 2) (x 10 13)
        have b21244 := hb (x 10 13)
        have b21245 := hb (x 10 2 && x 10 13)
        clear * - r21243 b21244 b21245 d21234
        omega
      have d21246 : (x 12 11).toNat = 1 := by
        have r21247 : 1 ≤ (x 12 11).toNat + (x 11 1 && x 11 12).toNat + (x 10 2 && x 10 13).toNat + (x 9 3 && x 9 14).toNat + (x 8 4).toNat := by have q := hcov11 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21248 := hb (x 8 4)
        have b21249 := hb (x 12 11)
        have b21250 := hb (x 11 1 && x 11 12)
        have b21251 := hb (x 10 2 && x 10 13)
        have b21252 := hb (x 9 3 && x 9 14)
        clear * - r21247 b21248 b21249 b21250 b21251 b21252 d21230 d21242 d21106 d21044
        omega
      have d21253 : (x 12 3).toNat = 1 := by
        have r21254 : (x 12 11).toNat ≤ (x 12 3).toNat := himp _ _ (hp11 12)
        have b21255 := hb (x 12 3)
        have b21256 := hb (x 12 11)
        clear * - r21254 b21255 b21256 d21246
        omega
      have d21257 : (x 15 12).toNat = 0 := by
        have r21258 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21259 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e21260 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b21261 := hb (x 12 3)
        have b21262 := hb (x 13 2)
        have b21263 := hb (x 14 13)
        have b21264 := hb (x 15 12)
        clear * - r21258 e21259 e21260 b21261 b21262 b21263 b21264 d21253
        omega
      have d21265 : (x 15 1 && x 15 12).toNat = 0 := by
        have r21266 := hand2 (x 15 1) (x 15 12)
        have b21267 := hb (x 15 12)
        have b21268 := hb (x 15 1 && x 15 12)
        clear * - r21266 b21267 b21268 d21257
        omega
      have d21269 : (x 14 13).toNat = 0 := by
        have r21270 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21271 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e21272 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b21273 := hb (x 12 3)
        have b21274 := hb (x 13 2)
        have b21275 := hb (x 14 13)
        have b21276 := hb (x 15 12)
        clear * - r21270 e21271 e21272 b21273 b21274 b21275 b21276 d21257 d21253
        omega
      have d21277 : (x 14 2 && x 14 13).toNat = 0 := by
        have r21278 := hand2 (x 14 2) (x 14 13)
        have b21279 := hb (x 14 13)
        have b21280 := hb (x 14 2 && x 14 13)
        clear * - r21278 b21279 b21280 d21269
        omega
      have d21281 : (x 13 2).toNat = 0 := by
        have r21282 : (x 15 12).toNat + (x 14 1 && x 14 13).toNat + (x 13 2 && x 13 14).toNat + (x 12 3).toNat = 1 := by have q := hd12 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21283 : (x 14 1 && x 14 13).toNat = (x 14 13).toNat := handr _ _ (fun h => hp13 14 (h))
        have e21284 : (x 13 2 && x 13 14).toNat = (x 13 2).toNat := handl _ _ (fun h => hp2 13 (h))
        have b21285 := hb (x 12 3)
        have b21286 := hb (x 13 2)
        have b21287 := hb (x 14 13)
        have b21288 := hb (x 15 12)
        clear * - r21282 e21283 e21284 b21285 b21286 b21287 b21288 d21257 d21269 d21253
        omega
      have d21289 : (x 10 1).toNat = 1 := by
        have r21290 := hand1 (x 10 1) (x 10 14)
        have b21291 := hb (x 10 1)
        have b21292 := hb (x 10 1 && x 10 14)
        clear * - r21290 b21291 b21292 d21177
        omega
      have d21293 : (x 11 14).toNat = 0 := by
        have r21294 : (x 11 14).toNat + (x 10 1).toNat = 1 := by have q := hd14 11; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21295 := hb (x 10 1)
        have b21296 := hb (x 11 14)
        clear * - r21294 b21295 b21296 d21289
        omega
      have d21297 : (x 11 1 && x 11 14).toNat = 0 := by
        have r21298 := hand2 (x 11 1) (x 11 14)
        have b21299 := hb (x 11 14)
        have b21300 := hb (x 11 1 && x 11 14)
        clear * - r21298 b21299 b21300 d21293
        omega
      have d21301 : (x 11 2).toNat = 0 := by
        have r21302 : (x 11 2).toNat ≤ (x 11 14).toNat := himp _ _ (hp2 11)
        have b21303 := hb (x 11 2)
        have b21304 := hb (x 11 14)
        clear * - r21302 b21303 b21304 d21293
        omega
      have d21305 : (x 10 2).toNat = 0 := by
        have r21306 : (x 12 12).toNat + (x 11 1 && x 11 13).toNat + (x 10 2 && x 10 14).toNat + (x 9 3).toNat = 1 := by have q := hd12 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21307 : (x 11 1 && x 11 13).toNat = (x 11 13).toNat := handr _ _ (fun h => hp13 11 (h))
        have e21308 : (x 10 2 && x 10 14).toNat = (x 10 2).toNat := handl _ _ (fun h => hp2 10 (h))
        have b21309 := hb (x 9 3)
        have b21310 := hb (x 10 2)
        have b21311 := hb (x 11 13)
        have b21312 := hb (x 12 12)
        clear * - r21306 e21307 e21308 b21309 b21310 b21311 b21312 d21149 d21165 d21145
        omega
      have d21313 : (x 12 13).toNat = 1 := by
        have r21314 : 1 ≤ (x 12 13).toNat + (x 11 1 && x 11 14).toNat + (x 10 2).toNat := by have q := hcov13 12; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21315 := hb (x 10 2)
        have b21316 := hb (x 12 13)
        have b21317 := hb (x 11 1 && x 11 14)
        clear * - r21314 b21315 b21316 b21317 d21297 d21305
        omega
      have d21318 : (x 12 1).toNat = 1 := by
        have r21319 : (x 12 13).toNat ≤ (x 12 1).toNat := himp _ _ (hp13 12)
        have b21320 := hb (x 12 1)
        have b21321 := hb (x 12 13)
        clear * - r21319 b21320 b21321 d21313
        omega
      have d21322 : (x 13 14).toNat = 0 := by
        have r21323 : (x 13 14).toNat + (x 12 1).toNat = 1 := by have q := hd14 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21324 := hb (x 12 1)
        have b21325 := hb (x 13 14)
        clear * - r21323 b21324 b21325 d21318
        omega
      have d21326 : (x 13 1 && x 13 14).toNat = 0 := by
        have r21327 := hand2 (x 13 1) (x 13 14)
        have b21328 := hb (x 13 14)
        have b21329 := hb (x 13 1 && x 13 14)
        clear * - r21327 b21328 b21329 d21322
        omega
      have d21330 : (x 12 2).toNat = 1 := by
        have r21331 : 1 ≤ (x 14 13).toNat + (x 13 1 && x 13 14).toNat + (x 12 2).toNat := by have q := hcov13 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21332 := hb (x 12 2)
        have b21333 := hb (x 14 13)
        have b21334 := hb (x 13 1 && x 13 14)
        clear * - r21331 b21332 b21333 b21334 d21269 d21326
        omega
      have d21335 : (x 14 12).toNat = 0 := by
        have r21336 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21337 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e21338 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b21339 := hb (x 11 3)
        have b21340 := hb (x 12 2)
        have b21341 := hb (x 13 13)
        have b21342 := hb (x 14 12)
        clear * - r21336 e21337 e21338 b21339 b21340 b21341 b21342 d21330
        omega
      have d21343 : (x 14 4).toNat = 0 := by
        have r21344 : (x 14 4).toNat ≤ (x 14 12).toNat := himp _ _ (hp4 14)
        have b21345 := hb (x 14 4)
        have b21346 := hb (x 14 12)
        clear * - r21344 b21345 b21346 d21335
        omega
      have d21347 : (x 14 4 && x 14 14).toNat = 0 := by
        have r21348 := hand1 (x 14 4) (x 14 14)
        have b21349 := hb (x 14 4)
        have b21350 := hb (x 14 4 && x 14 14)
        clear * - r21348 b21349 b21350 d21343
        omega
      have d21351 : (x 13 13).toNat = 0 := by
        have r21352 : (x 14 12).toNat + (x 13 1 && x 13 13).toNat + (x 12 2 && x 12 14).toNat + (x 11 3).toNat = 1 := by have q := hd12 14; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21353 : (x 13 1 && x 13 13).toNat = (x 13 13).toNat := handr _ _ (fun h => hp13 13 (h))
        have e21354 : (x 12 2 && x 12 14).toNat = (x 12 2).toNat := handl _ _ (fun h => hp2 12 (h))
        have b21355 := hb (x 11 3)
        have b21356 := hb (x 12 2)
        have b21357 := hb (x 13 13)
        have b21358 := hb (x 14 12)
        clear * - r21352 e21353 e21354 b21355 b21356 b21357 b21358 d21335 d21330
        omega
      have d21359 : (x 13 5).toNat = 0 := by
        have r21360 : (x 13 5).toNat ≤ (x 13 13).toNat := himp _ _ (hp5 13)
        have b21361 := hb (x 13 5)
        have b21362 := hb (x 13 13)
        clear * - r21360 b21361 b21362 d21351
        omega
      have d21363 : (x 13 3 && x 13 14).toNat = 0 := by
        have r21364 := hand2 (x 13 3) (x 13 14)
        have b21365 := hb (x 13 14)
        have b21366 := hb (x 13 3 && x 13 14)
        clear * - r21364 b21365 b21366 d21322
        omega
      have d21367 : (x 16 11).toNat = 1 := by
        have r21368 : 1 ≤ (x 16 11).toNat + (x 15 1 && x 15 12).toNat + (x 14 2 && x 14 13).toNat + (x 13 3 && x 13 14).toNat + (x 12 4).toNat := by have q := hcov11 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21369 := hb (x 12 4)
        have b21370 := hb (x 16 11)
        have b21371 := hb (x 15 1 && x 15 12)
        have b21372 := hb (x 14 2 && x 14 13)
        have b21373 := hb (x 13 3 && x 13 14)
        clear * - r21368 b21369 b21370 b21371 b21372 b21373 d21265 d21277 d21363 d21161
        omega
      have d21374 : (x 16 3).toNat = 1 := by
        have r21375 : (x 16 11).toNat ≤ (x 16 3).toNat := himp _ _ (hp11 16)
        have b21376 := hb (x 16 3)
        have b21377 := hb (x 16 11)
        clear * - r21375 b21376 b21377 d21367
        omega
      have d21378 : (x 19 12).toNat = 0 := by
        have r21379 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21380 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e21381 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b21382 := hb (x 16 3)
        have b21383 := hb (x 17 2)
        have b21384 := hb (x 18 13)
        have b21385 := hb (x 19 12)
        clear * - r21379 e21380 e21381 b21382 b21383 b21384 b21385 d21374
        omega
      have d21386 : (x 18 13).toNat = 0 := by
        have r21387 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21388 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e21389 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b21390 := hb (x 16 3)
        have b21391 := hb (x 17 2)
        have b21392 := hb (x 18 13)
        have b21393 := hb (x 19 12)
        clear * - r21387 e21388 e21389 b21390 b21391 b21392 b21393 d21378 d21374
        omega
      have d21394 : (x 17 2).toNat = 0 := by
        have r21395 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21396 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
        have e21397 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
        have b21398 := hb (x 16 3)
        have b21399 := hb (x 17 2)
        have b21400 := hb (x 18 13)
        have b21401 := hb (x 19 12)
        clear * - r21395 e21396 e21397 b21398 b21399 b21400 b21401 d21378 d21386 d21374
        omega
      have d21402 : (x 13 12).toNat = 0 := by
        have r21403 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21404 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e21405 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b21406 := hb (x 10 3)
        have b21407 := hb (x 11 2)
        have b21408 := hb (x 12 13)
        have b21409 := hb (x 13 12)
        clear * - r21403 e21404 e21405 b21406 b21407 b21408 b21409 d21313 d21301
        omega
      have d21410 : (x 13 4).toNat = 0 := by
        have r21411 : (x 13 4).toNat ≤ (x 13 12).toNat := himp _ _ (hp4 13)
        have b21412 := hb (x 13 4)
        have b21413 := hb (x 13 12)
        clear * - r21411 b21412 b21413 d21402
        omega
      have d21414 : (x 10 3).toNat = 0 := by
        have r21415 : (x 13 12).toNat + (x 12 1 && x 12 13).toNat + (x 11 2 && x 11 14).toNat + (x 10 3).toNat = 1 := by have q := hd12 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21416 : (x 12 1 && x 12 13).toNat = (x 12 13).toNat := handr _ _ (fun h => hp13 12 (h))
        have e21417 : (x 11 2 && x 11 14).toNat = (x 11 2).toNat := handl _ _ (fun h => hp2 11 (h))
        have b21418 := hb (x 10 3)
        have b21419 := hb (x 11 2)
        have b21420 := hb (x 12 13)
        have b21421 := hb (x 13 12)
        clear * - r21415 e21416 e21417 b21418 b21419 b21420 b21421 d21402 d21313 d21301
        omega
      have d21422 : (x 10 3 && x 10 14).toNat = 0 := by
        have r21423 := hand1 (x 10 3) (x 10 14)
        have b21424 := hb (x 10 3)
        have b21425 := hb (x 10 3 && x 10 14)
        clear * - r21423 b21424 b21425 d21414
        omega
      have d21426 : (x 13 11).toNat = 1 := by
        have r21427 : 1 ≤ (x 13 11).toNat + (x 12 1 && x 12 12).toNat + (x 11 2 && x 11 13).toNat + (x 10 3 && x 10 14).toNat + (x 9 4).toNat := by have q := hcov11 13; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21428 := hb (x 9 4)
        have b21429 := hb (x 13 11)
        have b21430 := hb (x 12 1 && x 12 12)
        have b21431 := hb (x 11 2 && x 11 13)
        have b21432 := hb (x 10 3 && x 10 14)
        clear * - r21427 b21428 b21429 b21430 b21431 b21432 d21157 d21173 d21422 d21122
        omega
      have d21433 : (x 13 3).toNat = 1 := by
        have r21434 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
        have b21435 := hb (x 13 3)
        have b21436 := hb (x 13 11)
        clear * - r21434 b21435 b21436 d21426
        omega
      have d21437 : (x 16 12).toNat = 0 := by
        have r21438 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21439 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e21440 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b21441 := hb (x 13 3)
        have b21442 := hb (x 14 2)
        have b21443 := hb (x 15 13)
        have b21444 := hb (x 16 12)
        clear * - r21438 e21439 e21440 b21441 b21442 b21443 b21444 d21433
        omega
      have d21445 : (x 16 1 && x 16 12).toNat = 0 := by
        have r21446 := hand2 (x 16 1) (x 16 12)
        have b21447 := hb (x 16 12)
        have b21448 := hb (x 16 1 && x 16 12)
        clear * - r21446 b21447 b21448 d21437
        omega
      have d21449 : (x 16 2 && x 16 12).toNat = 0 := by
        have r21450 := hand2 (x 16 2) (x 16 12)
        have b21451 := hb (x 16 12)
        have b21452 := hb (x 16 2 && x 16 12)
        clear * - r21450 b21451 b21452 d21437
        omega
      have d21453 : (x 15 13).toNat = 0 := by
        have r21454 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21455 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e21456 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b21457 := hb (x 13 3)
        have b21458 := hb (x 14 2)
        have b21459 := hb (x 15 13)
        have b21460 := hb (x 16 12)
        clear * - r21454 e21455 e21456 b21457 b21458 b21459 b21460 d21437 d21433
        omega
      have d21461 : (x 15 2 && x 15 13).toNat = 0 := by
        have r21462 := hand2 (x 15 2) (x 15 13)
        have b21463 := hb (x 15 13)
        have b21464 := hb (x 15 2 && x 15 13)
        clear * - r21462 b21463 b21464 d21453
        omega
      have d21465 : (x 15 3 && x 15 13).toNat = 0 := by
        have r21466 := hand2 (x 15 3) (x 15 13)
        have b21467 := hb (x 15 13)
        have b21468 := hb (x 15 3 && x 15 13)
        clear * - r21466 b21467 b21468 d21453
        omega
      have d21469 : (x 14 1 && x 14 14).toNat = 1 := by
        have r21470 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21471 := hb (x 13 2)
        have b21472 := hb (x 15 13)
        have b21473 := hb (x 14 1 && x 14 14)
        clear * - r21470 b21471 b21472 b21473 d21453 d21281
        omega
      have d21474 : (x 14 1).toNat = 1 := by
        have r21475 := hand1 (x 14 1) (x 14 14)
        have b21476 := hb (x 14 1)
        have b21477 := hb (x 14 1 && x 14 14)
        clear * - r21475 b21476 b21477 d21469
        omega
      have d21478 : (x 15 14).toNat = 0 := by
        have r21479 : (x 15 14).toNat + (x 14 1).toNat = 1 := by have q := hd14 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21480 := hb (x 14 1)
        have b21481 := hb (x 15 14)
        clear * - r21479 b21480 b21481 d21474
        omega
      have d21482 : (x 15 1 && x 15 14).toNat = 0 := by
        have r21483 := hand2 (x 15 1) (x 15 14)
        have b21484 := hb (x 15 14)
        have b21485 := hb (x 15 1 && x 15 14)
        clear * - r21483 b21484 b21485 d21478
        omega
      have d21486 : (x 15 2).toNat = 0 := by
        have r21487 : (x 15 2).toNat ≤ (x 15 14).toNat := himp _ _ (hp2 15)
        have b21488 := hb (x 15 2)
        have b21489 := hb (x 15 14)
        clear * - r21487 b21488 b21489 d21478
        omega
      have d21490 : (x 14 2).toNat = 0 := by
        have r21491 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21492 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e21493 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b21494 := hb (x 13 3)
        have b21495 := hb (x 14 2)
        have b21496 := hb (x 15 13)
        have b21497 := hb (x 16 12)
        clear * - r21491 e21492 e21493 b21494 b21495 b21496 b21497 d21437 d21453 d21433
        omega
      have d21498 : (x 16 13).toNat = 1 := by
        have r21499 : 1 ≤ (x 16 13).toNat + (x 15 1 && x 15 14).toNat + (x 14 2).toNat := by have q := hcov13 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21500 := hb (x 14 2)
        have b21501 := hb (x 16 13)
        have b21502 := hb (x 15 1 && x 15 14)
        clear * - r21499 b21500 b21501 b21502 d21482 d21490
        omega
      have d21503 : (x 17 12).toNat = 0 := by
        have r21504 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21505 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e21506 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b21507 := hb (x 14 3)
        have b21508 := hb (x 15 2)
        have b21509 := hb (x 16 13)
        have b21510 := hb (x 17 12)
        clear * - r21504 e21505 e21506 b21507 b21508 b21509 b21510 d21498 d21486
        omega
      have d21511 : (x 14 3).toNat = 0 := by
        have r21512 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21513 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e21514 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b21515 := hb (x 14 3)
        have b21516 := hb (x 15 2)
        have b21517 := hb (x 16 13)
        have b21518 := hb (x 17 12)
        clear * - r21512 e21513 e21514 b21515 b21516 b21517 b21518 d21503 d21498 d21486
        omega
      have d21519 : (x 14 3 && x 14 14).toNat = 0 := by
        have r21520 := hand1 (x 14 3) (x 14 14)
        have b21521 := hb (x 14 3)
        have b21522 := hb (x 14 3 && x 14 14)
        clear * - r21520 b21521 b21522 d21511
        omega
      have d21523 : (x 17 11).toNat = 1 := by
        have r21524 : 1 ≤ (x 17 11).toNat + (x 16 1 && x 16 12).toNat + (x 15 2 && x 15 13).toNat + (x 14 3 && x 14 14).toNat + (x 13 4).toNat := by have q := hcov11 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21525 := hb (x 13 4)
        have b21526 := hb (x 17 11)
        have b21527 := hb (x 16 1 && x 16 12)
        have b21528 := hb (x 15 2 && x 15 13)
        have b21529 := hb (x 14 3 && x 14 14)
        clear * - r21524 b21525 b21526 b21527 b21528 b21529 d21445 d21461 d21519 d21410
        omega
      have d21530 : (x 17 3).toNat = 1 := by
        have r21531 : (x 17 11).toNat ≤ (x 17 3).toNat := himp _ _ (hp11 17)
        have b21532 := hb (x 17 3)
        have b21533 := hb (x 17 11)
        clear * - r21531 b21532 b21533 d21523
        omega
      have d21534 : (x 20 12).toNat = 0 := by
        have r21535 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21536 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e21537 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b21538 := hb (x 17 3)
        have b21539 := hb (x 18 2)
        have b21540 := hb (x 19 13)
        have b21541 := hb (x 20 12)
        clear * - r21535 e21536 e21537 b21538 b21539 b21540 b21541 d21530
        omega
      have d21542 : (x 19 13).toNat = 0 := by
        have r21543 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21544 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e21545 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b21546 := hb (x 17 3)
        have b21547 := hb (x 18 2)
        have b21548 := hb (x 19 13)
        have b21549 := hb (x 20 12)
        clear * - r21543 e21544 e21545 b21546 b21547 b21548 b21549 d21534 d21530
        omega
      have d21550 : (x 18 1 && x 18 14).toNat = 1 := by
        have r21551 : 1 ≤ (x 19 13).toNat + (x 18 1 && x 18 14).toNat + (x 17 2).toNat := by have q := hcov13 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21552 := hb (x 17 2)
        have b21553 := hb (x 19 13)
        have b21554 := hb (x 18 1 && x 18 14)
        clear * - r21551 b21552 b21553 b21554 d21542 d21394
        omega
      have d21555 : (x 18 14).toNat = 1 := by
        have r21556 := hand2 (x 18 1) (x 18 14)
        have b21557 := hb (x 18 14)
        have b21558 := hb (x 18 1 && x 18 14)
        clear * - r21556 b21557 b21558 d21550
        omega
      have d21559 : (x 17 1).toNat = 0 := by
        have r21560 : (x 18 14).toNat + (x 17 1).toNat = 1 := by have q := hd14 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21561 := hb (x 17 1)
        have b21562 := hb (x 18 14)
        clear * - r21560 b21561 b21562 d21555
        omega
      have d21563 : (x 17 1 && x 17 11).toNat = 0 := by
        have r21564 := hand1 (x 17 1) (x 17 11)
        have b21565 := hb (x 17 1)
        have b21566 := hb (x 17 1 && x 17 11)
        clear * - r21564 b21565 b21566 d21559
        omega
      have d21567 : (x 18 2).toNat = 0 := by
        have r21568 : (x 20 12).toNat + (x 19 1 && x 19 13).toNat + (x 18 2 && x 18 14).toNat + (x 17 3).toNat = 1 := by have q := hd12 20; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21569 : (x 19 1 && x 19 13).toNat = (x 19 13).toNat := handr _ _ (fun h => hp13 19 (h))
        have e21570 : (x 18 2 && x 18 14).toNat = (x 18 2).toNat := handl _ _ (fun h => hp2 18 (h))
        have b21571 := hb (x 17 3)
        have b21572 := hb (x 18 2)
        have b21573 := hb (x 19 13)
        have b21574 := hb (x 20 12)
        clear * - r21568 e21569 e21570 b21571 b21572 b21573 b21574 d21534 d21542 d21530
        omega
      have d21575 : (x 18 10).toNat = 0 := by
        have r21576 : (x 18 10).toNat ≤ (x 18 2).toNat := himp _ _ (hp10 18)
        have b21577 := hb (x 18 2)
        have b21578 := hb (x 18 10)
        clear * - r21576 b21577 b21578 d21567
        omega
      have r21579 : 1 ≤ (x 18 10).toNat + (x 17 1 && x 17 11).toNat + (x 16 2 && x 16 12).toNat + (x 15 3 && x 15 13).toNat + (x 14 4 && x 14 14).toNat + (x 13 5).toNat := by have q := hcov10 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b21580 := hb (x 13 5)
      have b21581 := hb (x 18 10)
      have b21582 := hb (x 17 1 && x 17 11)
      have b21583 := hb (x 16 2 && x 16 12)
      have b21584 := hb (x 15 3 && x 15 13)
      have b21585 := hb (x 14 4 && x 14 14)
      linarith only [r21579, b21580, b21581, b21582, b21583, b21584, b21585, d21575, d21563, d21449, d21465, d21347, d21359]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00001_aux (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 5).toNat = 0)
    (g1 : (x 0 7).toNat = 1)
    (g2 : (x 0 8).toNat = 0)
    (g3 : (x 1 14).toNat = 1)
    (g4 : (x 2 13).toNat = 1)
    (g5 : (x 3 2).toNat = 0)
    (g6 : (x 3 4).toNat = 0)
    (g7 : (x 3 6).toNat = 0)
    (g8 : (x 3 12).toNat = 0)
    (g9 : (x 3 14).toNat = 0)
    (g10 : (x 3 5 && x 3 12).toNat = 0)
    (g11 : (x 3 4 && x 3 13).toNat = 0)
    (g12 : (x 3 2 && x 3 12).toNat = 0)
    (g13 : (x 1 4 && x 1 14).toNat = 0)
    (g14 : (x 3 1 && x 3 14).toNat = 0)
    : False := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by decide
  have hand1 : ∀ a b : Bool, (a && b).toNat ≤ a.toNat := by decide
  have hand2 : ∀ a b : Bool, (a && b).toNat ≤ b.toNat := by decide
  have handr : ∀ a b : Bool, (b = true → a = true) → (a && b).toNat = b.toNat := by decide
  have handl : ∀ a b : Bool, (a = true → b = true) → (a && b).toNat = a.toNat := by decide
  have himp : ∀ a b : Bool, (a = true → b = true) → a.toNat ≤ b.toNat := by decide
  have d21587 : (x 7 8).toNat = 0 := by
    have r21588 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e21589 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e21590 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e21591 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e21592 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e21593 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e21594 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b21595 := hb (x 0 7)
    have b21596 := hb (x 1 6)
    have b21597 := hb (x 2 5)
    have b21598 := hb (x 3 4)
    have b21599 := hb (x 4 11)
    have b21600 := hb (x 5 10)
    have b21601 := hb (x 6 9)
    have b21602 := hb (x 7 8)
    clear * - r21588 e21589 e21590 e21591 e21592 e21593 e21594 b21595 b21596 b21597 b21598 b21599 b21600 b21601 b21602 g6 g1
    omega
  have d21603 : (x 7 1 && x 7 8).toNat = 0 := by
    have r21604 := hand2 (x 7 1) (x 7 8)
    have b21605 := hb (x 7 8)
    have b21606 := hb (x 7 1 && x 7 8)
    clear * - r21604 b21605 b21606 d21587
    omega
  have d21607 : (x 6 9).toNat = 0 := by
    have r21608 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e21609 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e21610 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e21611 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e21612 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e21613 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e21614 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b21615 := hb (x 0 7)
    have b21616 := hb (x 1 6)
    have b21617 := hb (x 2 5)
    have b21618 := hb (x 3 4)
    have b21619 := hb (x 4 11)
    have b21620 := hb (x 5 10)
    have b21621 := hb (x 6 9)
    have b21622 := hb (x 7 8)
    clear * - r21608 e21609 e21610 e21611 e21612 e21613 e21614 b21615 b21616 b21617 b21618 b21619 b21620 b21621 b21622 d21587 g6 g1
    omega
  have d21623 : (x 6 2 && x 6 9).toNat = 0 := by
    have r21624 := hand2 (x 6 2) (x 6 9)
    have b21625 := hb (x 6 9)
    have b21626 := hb (x 6 2 && x 6 9)
    clear * - r21624 b21625 b21626 d21607
    omega
  have d21627 : (x 5 10).toNat = 0 := by
    have r21628 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e21629 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e21630 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e21631 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e21632 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e21633 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e21634 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b21635 := hb (x 0 7)
    have b21636 := hb (x 1 6)
    have b21637 := hb (x 2 5)
    have b21638 := hb (x 3 4)
    have b21639 := hb (x 4 11)
    have b21640 := hb (x 5 10)
    have b21641 := hb (x 6 9)
    have b21642 := hb (x 7 8)
    clear * - r21628 e21629 e21630 e21631 e21632 e21633 e21634 b21635 b21636 b21637 b21638 b21639 b21640 b21641 b21642 d21587 d21607 g6 g1
    omega
  have d21643 : (x 5 3 && x 5 10).toNat = 0 := by
    have r21644 := hand2 (x 5 3) (x 5 10)
    have b21645 := hb (x 5 10)
    have b21646 := hb (x 5 3 && x 5 10)
    clear * - r21644 b21645 b21646 d21627
    omega
  have d21647 : (x 4 11).toNat = 0 := by
    have r21648 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e21649 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e21650 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e21651 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e21652 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e21653 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e21654 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b21655 := hb (x 0 7)
    have b21656 := hb (x 1 6)
    have b21657 := hb (x 2 5)
    have b21658 := hb (x 3 4)
    have b21659 := hb (x 4 11)
    have b21660 := hb (x 5 10)
    have b21661 := hb (x 6 9)
    have b21662 := hb (x 7 8)
    clear * - r21648 e21649 e21650 e21651 e21652 e21653 e21654 b21655 b21656 b21657 b21658 b21659 b21660 b21661 b21662 d21587 d21607 d21627 g6 g1
    omega
  have d21663 : (x 4 1 && x 4 11).toNat = 0 := by
    have r21664 := hand2 (x 4 1) (x 4 11)
    have b21665 := hb (x 4 11)
    have b21666 := hb (x 4 1 && x 4 11)
    clear * - r21664 b21665 b21666 d21647
    omega
  have d21667 : (x 2 3 && x 2 13).toNat = 1 := by
    have r21668 : 1 ≤ (x 5 10).toNat + (x 4 1 && x 4 11).toNat + (x 3 2 && x 3 12).toNat + (x 2 3 && x 2 13).toNat + (x 1 4 && x 1 14).toNat + (x 0 5).toNat := by have q := hcov10 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b21669 := hb (x 0 5)
    have b21670 := hb (x 5 10)
    have b21671 := hb (x 4 1 && x 4 11)
    have b21672 := hb (x 3 2 && x 3 12)
    have b21673 := hb (x 2 3 && x 2 13)
    have b21674 := hb (x 1 4 && x 1 14)
    clear * - r21668 b21669 b21670 b21671 b21672 b21673 b21674 d21627 d21663 g12 g13 g0
    omega
  have d21675 : (x 2 3).toNat = 1 := by
    have r21676 := hand1 (x 2 3) (x 2 13)
    have b21677 := hb (x 2 3)
    have b21678 := hb (x 2 3 && x 2 13)
    clear * - r21676 b21677 b21678 d21667
    omega
  have d21679 : (x 5 12).toNat = 0 := by
    have r21680 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e21681 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e21682 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b21683 := hb (x 2 3)
    have b21684 := hb (x 3 2)
    have b21685 := hb (x 4 13)
    have b21686 := hb (x 5 12)
    clear * - r21680 e21681 e21682 b21683 b21684 b21685 b21686 g5 d21675
    omega
  have d21687 : (x 5 4).toNat = 0 := by
    have r21688 : (x 5 4).toNat ≤ (x 5 12).toNat := himp _ _ (hp4 5)
    have b21689 := hb (x 5 4)
    have b21690 := hb (x 5 12)
    clear * - r21688 b21689 b21690 d21679
    omega
  have d21691 : (x 4 13).toNat = 0 := by
    have r21692 : (x 5 12).toNat + (x 4 1 && x 4 13).toNat + (x 3 2 && x 3 14).toNat + (x 2 3).toNat = 1 := by have q := hd12 5; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e21693 : (x 4 1 && x 4 13).toNat = (x 4 13).toNat := handr _ _ (fun h => hp13 4 (h))
    have e21694 : (x 3 2 && x 3 14).toNat = (x 3 2).toNat := handl _ _ (fun h => hp2 3 (h))
    have b21695 := hb (x 2 3)
    have b21696 := hb (x 3 2)
    have b21697 := hb (x 4 13)
    have b21698 := hb (x 5 12)
    clear * - r21692 e21693 e21694 b21695 b21696 b21697 b21698 d21679 g5 d21675
    omega
  have d21699 : (x 4 5).toNat = 0 := by
    have r21700 : (x 4 5).toNat ≤ (x 4 13).toNat := himp _ _ (hp5 4)
    have b21701 := hb (x 4 5)
    have b21702 := hb (x 4 13)
    clear * - r21700 b21701 b21702 d21691
    omega
  have d21703 : (x 2 2).toNat = 1 := by
    have r21704 : 1 ≤ (x 4 13).toNat + (x 3 1 && x 3 14).toNat + (x 2 2).toNat := by have q := hcov13 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have b21705 := hb (x 2 2)
    have b21706 := hb (x 4 13)
    have b21707 := hb (x 3 1 && x 3 14)
    clear * - r21704 b21705 b21706 b21707 d21691 g14
    omega
  have d21708 : (x 4 12).toNat = 0 := by
    have r21709 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e21710 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e21711 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b21712 := hb (x 1 3)
    have b21713 := hb (x 2 2)
    have b21714 := hb (x 3 13)
    have b21715 := hb (x 4 12)
    clear * - r21709 e21710 e21711 b21712 b21713 b21714 b21715 d21703
    omega
  have d21716 : (x 4 3 && x 4 12).toNat = 0 := by
    have r21717 := hand2 (x 4 3) (x 4 12)
    have b21718 := hb (x 4 12)
    have b21719 := hb (x 4 3 && x 4 12)
    clear * - r21717 b21718 b21719 d21708
    omega
  have d21720 : (x 4 4).toNat = 0 := by
    have r21721 : (x 4 4).toNat ≤ (x 4 12).toNat := himp _ _ (hp4 4)
    have b21722 := hb (x 4 4)
    have b21723 := hb (x 4 12)
    clear * - r21721 b21722 b21723 d21708
    omega
  have d21724 : (x 4 4 && x 4 11).toNat = 0 := by
    have r21725 := hand1 (x 4 4) (x 4 11)
    have b21726 := hb (x 4 4)
    have b21727 := hb (x 4 4 && x 4 11)
    clear * - r21725 b21726 b21727 d21720
    omega
  have d21728 : (x 3 13).toNat = 0 := by
    have r21729 : (x 4 12).toNat + (x 3 1 && x 3 13).toNat + (x 2 2 && x 2 14).toNat + (x 1 3).toNat = 1 := by have q := hd12 4; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e21730 : (x 3 1 && x 3 13).toNat = (x 3 13).toNat := handr _ _ (fun h => hp13 3 (h))
    have e21731 : (x 2 2 && x 2 14).toNat = (x 2 2).toNat := handl _ _ (fun h => hp2 2 (h))
    have b21732 := hb (x 1 3)
    have b21733 := hb (x 2 2)
    have b21734 := hb (x 3 13)
    have b21735 := hb (x 4 12)
    clear * - r21729 e21730 e21731 b21732 b21733 b21734 b21735 d21708 d21703
    omega
  have d21736 : (x 3 5).toNat = 0 := by
    have r21737 : (x 3 5).toNat ≤ (x 3 13).toNat := himp _ _ (hp5 3)
    have b21738 := hb (x 3 5)
    have b21739 := hb (x 3 13)
    clear * - r21737 b21738 b21739 d21728
    omega
  have d21740 : (x 2 5).toNat = 0 := by
    have r21741 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e21742 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e21743 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e21744 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e21745 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e21746 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e21747 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b21748 := hb (x 0 7)
    have b21749 := hb (x 1 6)
    have b21750 := hb (x 2 5)
    have b21751 := hb (x 3 4)
    have b21752 := hb (x 4 11)
    have b21753 := hb (x 5 10)
    have b21754 := hb (x 6 9)
    have b21755 := hb (x 7 8)
    clear * - r21741 e21742 e21743 e21744 e21745 e21746 e21747 b21748 b21749 b21750 b21751 b21752 b21753 b21754 b21755 d21587 d21607 d21627 d21647 g6 g1
    omega
  have d21756 : (x 2 5 && x 2 14).toNat = 0 := by
    have r21757 := hand1 (x 2 5) (x 2 14)
    have b21758 := hb (x 2 5)
    have b21759 := hb (x 2 5 && x 2 14)
    clear * - r21757 b21758 b21759 d21740
    omega
  have d21760 : (x 1 6).toNat = 0 := by
    have r21761 : (x 7 8).toNat + (x 6 1 && x 6 9).toNat + (x 5 2 && x 5 10).toNat + (x 4 3 && x 4 11).toNat + (x 3 4 && x 3 12).toNat + (x 2 5 && x 2 13).toNat + (x 1 6 && x 1 14).toNat + (x 0 7).toNat = 1 := by have q := hd8 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e21762 : (x 6 1 && x 6 9).toNat = (x 6 9).toNat := handr _ _ (fun h => hp9 6 (h))
    have e21763 : (x 5 2 && x 5 10).toNat = (x 5 10).toNat := handr _ _ (fun h => hp10 5 (h))
    have e21764 : (x 4 3 && x 4 11).toNat = (x 4 11).toNat := handr _ _ (fun h => hp11 4 (h))
    have e21765 : (x 3 4 && x 3 12).toNat = (x 3 4).toNat := handl _ _ (fun h => hp4 3 (h))
    have e21766 : (x 2 5 && x 2 13).toNat = (x 2 5).toNat := handl _ _ (fun h => hp5 2 (h))
    have e21767 : (x 1 6 && x 1 14).toNat = (x 1 6).toNat := handl _ _ (fun h => hp6 1 (h))
    have b21768 := hb (x 0 7)
    have b21769 := hb (x 1 6)
    have b21770 := hb (x 2 5)
    have b21771 := hb (x 3 4)
    have b21772 := hb (x 4 11)
    have b21773 := hb (x 5 10)
    have b21774 := hb (x 6 9)
    have b21775 := hb (x 7 8)
    clear * - r21761 e21762 e21763 e21764 e21765 e21766 e21767 b21768 b21769 b21770 b21771 b21772 b21773 b21774 b21775 d21587 d21607 d21627 d21647 g6 d21740 g1
    omega
  cases h21776 : x 1 7
  · have f21777 : (x 1 7).toNat = 0 := by rw [h21776]; rfl
    have d21778 : (x 1 7 && x 1 14).toNat = 0 := by
      have r21779 := hand1 (x 1 7) (x 1 14)
      have b21780 := hb (x 1 7)
      have b21781 := hb (x 1 7 && x 1 14)
      clear * - r21779 b21780 b21781 f21777
      omega
    cases h21782 : x 2 6
    · have f21783 : (x 2 6).toNat = 0 := by rw [h21782]; rfl
      have d21784 : (x 2 6 && x 2 13).toNat = 0 := by
        have r21785 := hand1 (x 2 6) (x 2 13)
        have b21786 := hb (x 2 6)
        have b21787 := hb (x 2 6 && x 2 13)
        clear * - r21785 b21786 b21787 f21783
        omega
      have d21788 : (x 8 7).toNat = 1 := by
        have r21789 : 1 ≤ (x 8 7).toNat + (x 7 1 && x 7 8).toNat + (x 6 2 && x 6 9).toNat + (x 5 3 && x 5 10).toNat + (x 4 4 && x 4 11).toNat + (x 3 5 && x 3 12).toNat + (x 2 6 && x 2 13).toNat + (x 1 7 && x 1 14).toNat + (x 0 8).toNat := by have q := hcov7 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21790 := hb (x 0 8)
        have b21791 := hb (x 8 7)
        have b21792 := hb (x 7 1 && x 7 8)
        have b21793 := hb (x 6 2 && x 6 9)
        have b21794 := hb (x 5 3 && x 5 10)
        have b21795 := hb (x 4 4 && x 4 11)
        have b21796 := hb (x 3 5 && x 3 12)
        have b21797 := hb (x 2 6 && x 2 13)
        have b21798 := hb (x 1 7 && x 1 14)
        clear * - r21789 b21790 b21791 b21792 b21793 b21794 b21795 b21796 b21797 b21798 d21603 d21623 d21643 d21724 g10 d21784 d21778 g2
        omega
      have d21799 : (x 15 8).toNat = 0 := by
        have r21800 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21801 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e21802 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e21803 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e21804 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e21805 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e21806 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b21807 := hb (x 8 7)
        have b21808 := hb (x 9 6)
        have b21809 := hb (x 10 5)
        have b21810 := hb (x 11 4)
        have b21811 := hb (x 12 11)
        have b21812 := hb (x 13 10)
        have b21813 := hb (x 14 9)
        have b21814 := hb (x 15 8)
        clear * - r21800 e21801 e21802 e21803 e21804 e21805 e21806 b21807 b21808 b21809 b21810 b21811 b21812 b21813 b21814 d21788
        omega
      have d21815 : (x 15 1 && x 15 8).toNat = 0 := by
        have r21816 := hand2 (x 15 1) (x 15 8)
        have b21817 := hb (x 15 8)
        have b21818 := hb (x 15 1 && x 15 8)
        clear * - r21816 b21817 b21818 d21799
        omega
      have d21819 : (x 14 9).toNat = 0 := by
        have r21820 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21821 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e21822 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e21823 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e21824 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e21825 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e21826 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b21827 := hb (x 8 7)
        have b21828 := hb (x 9 6)
        have b21829 := hb (x 10 5)
        have b21830 := hb (x 11 4)
        have b21831 := hb (x 12 11)
        have b21832 := hb (x 13 10)
        have b21833 := hb (x 14 9)
        have b21834 := hb (x 15 8)
        clear * - r21820 e21821 e21822 e21823 e21824 e21825 e21826 b21827 b21828 b21829 b21830 b21831 b21832 b21833 b21834 d21799 d21788
        omega
      have d21835 : (x 14 2 && x 14 9).toNat = 0 := by
        have r21836 := hand2 (x 14 2) (x 14 9)
        have b21837 := hb (x 14 9)
        have b21838 := hb (x 14 2 && x 14 9)
        clear * - r21836 b21837 b21838 d21819
        omega
      have d21839 : (x 13 10).toNat = 0 := by
        have r21840 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21841 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e21842 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e21843 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e21844 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e21845 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e21846 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b21847 := hb (x 8 7)
        have b21848 := hb (x 9 6)
        have b21849 := hb (x 10 5)
        have b21850 := hb (x 11 4)
        have b21851 := hb (x 12 11)
        have b21852 := hb (x 13 10)
        have b21853 := hb (x 14 9)
        have b21854 := hb (x 15 8)
        clear * - r21840 e21841 e21842 e21843 e21844 e21845 e21846 b21847 b21848 b21849 b21850 b21851 b21852 b21853 b21854 d21799 d21819 d21788
        omega
      have d21855 : (x 13 3 && x 13 10).toNat = 0 := by
        have r21856 := hand2 (x 13 3) (x 13 10)
        have b21857 := hb (x 13 10)
        have b21858 := hb (x 13 3 && x 13 10)
        clear * - r21856 b21857 b21858 d21839
        omega
      have d21859 : (x 12 11).toNat = 0 := by
        have r21860 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21861 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e21862 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e21863 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e21864 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e21865 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e21866 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b21867 := hb (x 8 7)
        have b21868 := hb (x 9 6)
        have b21869 := hb (x 10 5)
        have b21870 := hb (x 11 4)
        have b21871 := hb (x 12 11)
        have b21872 := hb (x 13 10)
        have b21873 := hb (x 14 9)
        have b21874 := hb (x 15 8)
        clear * - r21860 e21861 e21862 e21863 e21864 e21865 e21866 b21867 b21868 b21869 b21870 b21871 b21872 b21873 b21874 d21799 d21819 d21839 d21788
        omega
      have d21875 : (x 12 4 && x 12 11).toNat = 0 := by
        have r21876 := hand2 (x 12 4) (x 12 11)
        have b21877 := hb (x 12 11)
        have b21878 := hb (x 12 4 && x 12 11)
        clear * - r21876 b21877 b21878 d21859
        omega
      have d21879 : (x 11 4).toNat = 0 := by
        have r21880 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21881 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e21882 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e21883 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e21884 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e21885 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e21886 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b21887 := hb (x 8 7)
        have b21888 := hb (x 9 6)
        have b21889 := hb (x 10 5)
        have b21890 := hb (x 11 4)
        have b21891 := hb (x 12 11)
        have b21892 := hb (x 13 10)
        have b21893 := hb (x 14 9)
        have b21894 := hb (x 15 8)
        clear * - r21880 e21881 e21882 e21883 e21884 e21885 e21886 b21887 b21888 b21889 b21890 b21891 b21892 b21893 b21894 d21799 d21819 d21839 d21859 d21788
        omega
      have d21895 : (x 11 4 && x 11 14).toNat = 0 := by
        have r21896 := hand1 (x 11 4) (x 11 14)
        have b21897 := hb (x 11 4)
        have b21898 := hb (x 11 4 && x 11 14)
        clear * - r21896 b21897 b21898 d21879
        omega
      have d21899 : (x 11 4 && x 11 13).toNat = 0 := by
        have r21900 := hand1 (x 11 4) (x 11 13)
        have b21901 := hb (x 11 4)
        have b21902 := hb (x 11 4 && x 11 13)
        clear * - r21900 b21901 b21902 d21879
        omega
      have d21903 : (x 10 5).toNat = 0 := by
        have r21904 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21905 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e21906 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e21907 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e21908 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e21909 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e21910 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b21911 := hb (x 8 7)
        have b21912 := hb (x 9 6)
        have b21913 := hb (x 10 5)
        have b21914 := hb (x 11 4)
        have b21915 := hb (x 12 11)
        have b21916 := hb (x 13 10)
        have b21917 := hb (x 14 9)
        have b21918 := hb (x 15 8)
        clear * - r21904 e21905 e21906 e21907 e21908 e21909 e21910 b21911 b21912 b21913 b21914 b21915 b21916 b21917 b21918 d21799 d21819 d21839 d21859 d21879 d21788
        omega
      have d21919 : (x 10 5 && x 10 14).toNat = 0 := by
        have r21920 := hand1 (x 10 5) (x 10 14)
        have b21921 := hb (x 10 5)
        have b21922 := hb (x 10 5 && x 10 14)
        clear * - r21920 b21921 b21922 d21903
        omega
      have d21923 : (x 9 6).toNat = 0 := by
        have r21924 : (x 15 8).toNat + (x 14 1 && x 14 9).toNat + (x 13 2 && x 13 10).toNat + (x 12 3 && x 12 11).toNat + (x 11 4 && x 11 12).toNat + (x 10 5 && x 10 13).toNat + (x 9 6 && x 9 14).toNat + (x 8 7).toNat = 1 := by have q := hd8 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e21925 : (x 14 1 && x 14 9).toNat = (x 14 9).toNat := handr _ _ (fun h => hp9 14 (h))
        have e21926 : (x 13 2 && x 13 10).toNat = (x 13 10).toNat := handr _ _ (fun h => hp10 13 (h))
        have e21927 : (x 12 3 && x 12 11).toNat = (x 12 11).toNat := handr _ _ (fun h => hp11 12 (h))
        have e21928 : (x 11 4 && x 11 12).toNat = (x 11 4).toNat := handl _ _ (fun h => hp4 11 (h))
        have e21929 : (x 10 5 && x 10 13).toNat = (x 10 5).toNat := handl _ _ (fun h => hp5 10 (h))
        have e21930 : (x 9 6 && x 9 14).toNat = (x 9 6).toNat := handl _ _ (fun h => hp6 9 (h))
        have b21931 := hb (x 8 7)
        have b21932 := hb (x 9 6)
        have b21933 := hb (x 10 5)
        have b21934 := hb (x 11 4)
        have b21935 := hb (x 12 11)
        have b21936 := hb (x 13 10)
        have b21937 := hb (x 14 9)
        have b21938 := hb (x 15 8)
        clear * - r21924 e21925 e21926 e21927 e21928 e21929 e21930 b21931 b21932 b21933 b21934 b21935 b21936 b21937 b21938 d21799 d21819 d21839 d21859 d21879 d21903 d21788
        omega
      have d21939 : (x 14 1).toNat = 0 := by
        have r21940 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21941 := hb (x 1 14)
        have b21942 := hb (x 2 13)
        have b21943 := hb (x 3 12)
        have b21944 := hb (x 4 11)
        have b21945 := hb (x 5 10)
        have b21946 := hb (x 6 9)
        have b21947 := hb (x 7 8)
        have b21948 := hb (x 8 7)
        have b21949 := hb (x 9 6)
        have b21950 := hb (x 10 5)
        have b21951 := hb (x 11 4)
        have b21952 := hb (x 12 3)
        have b21953 := hb (x 13 2)
        have b21954 := hb (x 14 1)
        clear * - r21940 b21941 b21942 b21943 b21944 b21945 b21946 b21947 b21948 b21949 b21950 b21951 b21952 b21953 b21954 d21879 d21903 d21923 d21788 d21587 d21607 d21627 d21647 g8 g4 g3
        omega
      have d21955 : (x 14 1 && x 14 14).toNat = 0 := by
        have r21956 := hand1 (x 14 1) (x 14 14)
        have b21957 := hb (x 14 1)
        have b21958 := hb (x 14 1 && x 14 14)
        clear * - r21956 b21957 b21958 d21939
        omega
      have d21959 : (x 14 1 && x 14 12).toNat = 0 := by
        have r21960 := hand1 (x 14 1) (x 14 12)
        have b21961 := hb (x 14 1)
        have b21962 := hb (x 14 1 && x 14 12)
        clear * - r21960 b21961 b21962 d21939
        omega
      have d21963 : (x 14 1 && x 14 11).toNat = 0 := by
        have r21964 := hand1 (x 14 1) (x 14 11)
        have b21965 := hb (x 14 1)
        have b21966 := hb (x 14 1 && x 14 11)
        clear * - r21964 b21965 b21966 d21939
        omega
      have d21967 : (x 14 1 && x 14 10).toNat = 0 := by
        have r21968 := hand1 (x 14 1) (x 14 10)
        have b21969 := hb (x 14 1)
        have b21970 := hb (x 14 1 && x 14 10)
        clear * - r21968 b21969 b21970 d21939
        omega
      have d21971 : (x 13 2).toNat = 0 := by
        have r21972 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b21973 := hb (x 1 14)
        have b21974 := hb (x 2 13)
        have b21975 := hb (x 3 12)
        have b21976 := hb (x 4 11)
        have b21977 := hb (x 5 10)
        have b21978 := hb (x 6 9)
        have b21979 := hb (x 7 8)
        have b21980 := hb (x 8 7)
        have b21981 := hb (x 9 6)
        have b21982 := hb (x 10 5)
        have b21983 := hb (x 11 4)
        have b21984 := hb (x 12 3)
        have b21985 := hb (x 13 2)
        have b21986 := hb (x 14 1)
        clear * - r21972 b21973 b21974 b21975 b21976 b21977 b21978 b21979 b21980 b21981 b21982 b21983 b21984 b21985 b21986 d21939 d21879 d21903 d21923 d21788 d21587 d21607 d21627 d21647 g8 g4 g3
        omega
      have d21987 : (x 13 2 && x 13 13).toNat = 0 := by
        have r21988 := hand1 (x 13 2) (x 13 13)
        have b21989 := hb (x 13 2)
        have b21990 := hb (x 13 2 && x 13 13)
        clear * - r21988 b21989 b21990 d21971
        omega
      have d21991 : (x 13 2 && x 13 12).toNat = 0 := by
        have r21992 := hand1 (x 13 2) (x 13 12)
        have b21993 := hb (x 13 2)
        have b21994 := hb (x 13 2 && x 13 12)
        clear * - r21992 b21993 b21994 d21971
        omega
      have d21995 : (x 13 2 && x 13 11).toNat = 0 := by
        have r21996 := hand1 (x 13 2) (x 13 11)
        have b21997 := hb (x 13 2)
        have b21998 := hb (x 13 2 && x 13 11)
        clear * - r21996 b21997 b21998 d21971
        omega
      have d21999 : (x 15 13).toNat = 1 := by
        have r22000 : 1 ≤ (x 15 13).toNat + (x 14 1 && x 14 14).toNat + (x 13 2).toNat := by have q := hcov13 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22001 := hb (x 13 2)
        have b22002 := hb (x 15 13)
        have b22003 := hb (x 14 1 && x 14 14)
        clear * - r22000 b22001 b22002 b22003 d21955 d21971
        omega
      have d22004 : (x 15 1).toNat = 1 := by
        have r22005 : (x 15 13).toNat ≤ (x 15 1).toNat := himp _ _ (hp13 15)
        have b22006 := hb (x 15 1)
        have b22007 := hb (x 15 13)
        clear * - r22005 b22006 b22007 d21999
        omega
      have d22008 : (x 16 14).toNat = 0 := by
        have r22009 : (x 16 14).toNat + (x 15 1).toNat = 1 := by have q := hd14 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22010 := hb (x 15 1)
        have b22011 := hb (x 16 14)
        clear * - r22009 b22010 b22011 d22004
        omega
      have d22012 : (x 16 1 && x 16 14).toNat = 0 := by
        have r22013 := hand2 (x 16 1) (x 16 14)
        have b22014 := hb (x 16 14)
        have b22015 := hb (x 16 1 && x 16 14)
        clear * - r22013 b22014 b22015 d22008
        omega
      have d22016 : (x 16 6).toNat = 0 := by
        have r22017 : (x 16 6).toNat ≤ (x 16 14).toNat := himp _ _ (hp6 16)
        have b22018 := hb (x 16 6)
        have b22019 := hb (x 16 14)
        clear * - r22017 b22018 b22019 d22008
        omega
      have d22020 : (x 16 2).toNat = 0 := by
        have r22021 : (x 16 2).toNat ≤ (x 16 14).toNat := himp _ _ (hp2 16)
        have b22022 := hb (x 16 2)
        have b22023 := hb (x 16 14)
        clear * - r22021 b22022 b22023 d22008
        omega
      have d22024 : (x 16 12).toNat = 0 := by
        have r22025 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22026 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e22027 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b22028 := hb (x 13 3)
        have b22029 := hb (x 14 2)
        have b22030 := hb (x 15 13)
        have b22031 := hb (x 16 12)
        clear * - r22025 e22026 e22027 b22028 b22029 b22030 b22031 d21999
        omega
      have d22032 : (x 14 2).toNat = 0 := by
        have r22033 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22034 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e22035 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b22036 := hb (x 13 3)
        have b22037 := hb (x 14 2)
        have b22038 := hb (x 15 13)
        have b22039 := hb (x 16 12)
        clear * - r22033 e22034 e22035 b22036 b22037 b22038 b22039 d22024 d21999
        omega
      have d22040 : (x 14 10).toNat = 0 := by
        have r22041 : (x 14 10).toNat ≤ (x 14 2).toNat := himp _ _ (hp10 14)
        have b22042 := hb (x 14 2)
        have b22043 := hb (x 14 10)
        clear * - r22041 b22042 b22043 d22032
        omega
      have d22044 : (x 13 3).toNat = 0 := by
        have r22045 : (x 16 12).toNat + (x 15 1 && x 15 13).toNat + (x 14 2 && x 14 14).toNat + (x 13 3).toNat = 1 := by have q := hd12 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22046 : (x 15 1 && x 15 13).toNat = (x 15 13).toNat := handr _ _ (fun h => hp13 15 (h))
        have e22047 : (x 14 2 && x 14 14).toNat = (x 14 2).toNat := handl _ _ (fun h => hp2 14 (h))
        have b22048 := hb (x 13 3)
        have b22049 := hb (x 14 2)
        have b22050 := hb (x 15 13)
        have b22051 := hb (x 16 12)
        clear * - r22045 e22046 e22047 b22048 b22049 b22050 b22051 d22024 d21999 d22032
        omega
      have d22052 : (x 13 11).toNat = 0 := by
        have r22053 : (x 13 11).toNat ≤ (x 13 3).toNat := himp _ _ (hp11 13)
        have b22054 := hb (x 13 3)
        have b22055 := hb (x 13 11)
        clear * - r22053 b22054 b22055 d22044
        omega
      have d22056 : (x 12 3).toNat = 0 := by
        have r22057 : (x 14 1).toNat + (x 13 2).toNat + (x 12 3).toNat + (x 11 4).toNat + (x 10 5).toNat + (x 9 6).toNat + (x 8 7).toNat + (x 7 8).toNat + (x 6 9).toNat + (x 5 10).toNat + (x 4 11).toNat + (x 3 12).toNat + (x 2 13).toNat + (x 1 14).toNat = 3 := by have q := hcount 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22058 := hb (x 1 14)
        have b22059 := hb (x 2 13)
        have b22060 := hb (x 3 12)
        have b22061 := hb (x 4 11)
        have b22062 := hb (x 5 10)
        have b22063 := hb (x 6 9)
        have b22064 := hb (x 7 8)
        have b22065 := hb (x 8 7)
        have b22066 := hb (x 9 6)
        have b22067 := hb (x 10 5)
        have b22068 := hb (x 11 4)
        have b22069 := hb (x 12 3)
        have b22070 := hb (x 13 2)
        have b22071 := hb (x 14 1)
        clear * - r22057 b22058 b22059 b22060 b22061 b22062 b22063 b22064 b22065 b22066 b22067 b22068 b22069 b22070 b22071 d21939 d21971 d21879 d21903 d21923 d21788 d21587 d21607 d21627 d21647 g8 g4 g3
        omega
      have d22072 : (x 12 3 && x 12 14).toNat = 0 := by
        have r22073 := hand1 (x 12 3) (x 12 14)
        have b22074 := hb (x 12 3)
        have b22075 := hb (x 12 3 && x 12 14)
        clear * - r22073 b22074 b22075 d22056
        omega
      have d22076 : (x 15 11).toNat = 1 := by
        have r22077 : 1 ≤ (x 15 11).toNat + (x 14 1 && x 14 12).toNat + (x 13 2 && x 13 13).toNat + (x 12 3 && x 12 14).toNat + (x 11 4).toNat := by have q := hcov11 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22078 := hb (x 11 4)
        have b22079 := hb (x 15 11)
        have b22080 := hb (x 14 1 && x 14 12)
        have b22081 := hb (x 13 2 && x 13 13)
        have b22082 := hb (x 12 3 && x 12 14)
        clear * - r22077 b22078 b22079 b22080 b22081 b22082 d21959 d21987 d22072 d21879
        omega
      have d22083 : (x 15 3).toNat = 1 := by
        have r22084 : (x 15 11).toNat ≤ (x 15 3).toNat := himp _ _ (hp11 15)
        have b22085 := hb (x 15 3)
        have b22086 := hb (x 15 11)
        clear * - r22084 b22085 b22086 d22076
        omega
      have d22087 : (x 18 12).toNat = 0 := by
        have r22088 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22089 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
        have e22090 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
        have b22091 := hb (x 15 3)
        have b22092 := hb (x 16 2)
        have b22093 := hb (x 17 13)
        have b22094 := hb (x 18 12)
        clear * - r22088 e22089 e22090 b22091 b22092 b22093 b22094 d22020 d22083
        omega
      have d22095 : (x 18 4).toNat = 0 := by
        have r22096 : (x 18 4).toNat ≤ (x 18 12).toNat := himp _ _ (hp4 18)
        have b22097 := hb (x 18 4)
        have b22098 := hb (x 18 12)
        clear * - r22096 b22097 b22098 d22087
        omega
      have d22099 : (x 18 4 && x 18 13).toNat = 0 := by
        have r22100 := hand1 (x 18 4) (x 18 13)
        have b22101 := hb (x 18 4)
        have b22102 := hb (x 18 4 && x 18 13)
        clear * - r22100 b22101 b22102 d22095
        omega
      have d22103 : (x 17 13).toNat = 0 := by
        have r22104 : (x 18 12).toNat + (x 17 1 && x 17 13).toNat + (x 16 2 && x 16 14).toNat + (x 15 3).toNat = 1 := by have q := hd12 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22105 : (x 17 1 && x 17 13).toNat = (x 17 13).toNat := handr _ _ (fun h => hp13 17 (h))
        have e22106 : (x 16 2 && x 16 14).toNat = (x 16 2).toNat := handl _ _ (fun h => hp2 16 (h))
        have b22107 := hb (x 15 3)
        have b22108 := hb (x 16 2)
        have b22109 := hb (x 17 13)
        have b22110 := hb (x 18 12)
        clear * - r22104 e22105 e22106 b22107 b22108 b22109 b22110 d22087 d22020 d22083
        omega
      have d22111 : (x 17 5).toNat = 0 := by
        have r22112 : (x 17 5).toNat ≤ (x 17 13).toNat := himp _ _ (hp5 17)
        have b22113 := hb (x 17 5)
        have b22114 := hb (x 17 13)
        clear * - r22112 b22113 b22114 d22103
        omega
      have d22115 : (x 17 5 && x 17 14).toNat = 0 := by
        have r22116 := hand1 (x 17 5) (x 17 14)
        have b22117 := hb (x 17 5)
        have b22118 := hb (x 17 5 && x 17 14)
        clear * - r22116 b22117 b22118 d22111
        omega
      have d22119 : (x 15 2).toNat = 1 := by
        have r22120 : 1 ≤ (x 17 13).toNat + (x 16 1 && x 16 14).toNat + (x 15 2).toNat := by have q := hcov13 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22121 := hb (x 15 2)
        have b22122 := hb (x 17 13)
        have b22123 := hb (x 16 1 && x 16 14)
        clear * - r22120 b22121 b22122 b22123 d22103 d22012
        omega
      have d22124 : (x 17 12).toNat = 0 := by
        have r22125 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22126 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e22127 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b22128 := hb (x 14 3)
        have b22129 := hb (x 15 2)
        have b22130 := hb (x 16 13)
        have b22131 := hb (x 17 12)
        clear * - r22125 e22126 e22127 b22128 b22129 b22130 b22131 d22119
        omega
      have d22132 : (x 16 13).toNat = 0 := by
        have r22133 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22134 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e22135 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b22136 := hb (x 14 3)
        have b22137 := hb (x 15 2)
        have b22138 := hb (x 16 13)
        have b22139 := hb (x 17 12)
        clear * - r22133 e22134 e22135 b22136 b22137 b22138 b22139 d22124 d22119
        omega
      have d22140 : (x 14 3).toNat = 0 := by
        have r22141 : (x 17 12).toNat + (x 16 1 && x 16 13).toNat + (x 15 2 && x 15 14).toNat + (x 14 3).toNat = 1 := by have q := hd12 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22142 : (x 16 1 && x 16 13).toNat = (x 16 13).toNat := handr _ _ (fun h => hp13 16 (h))
        have e22143 : (x 15 2 && x 15 14).toNat = (x 15 2).toNat := handl _ _ (fun h => hp2 15 (h))
        have b22144 := hb (x 14 3)
        have b22145 := hb (x 15 2)
        have b22146 := hb (x 16 13)
        have b22147 := hb (x 17 12)
        clear * - r22141 e22142 e22143 b22144 b22145 b22146 b22147 d22124 d22132 d22119
        omega
      have d22148 : (x 14 11).toNat = 0 := by
        have r22149 : (x 14 11).toNat ≤ (x 14 3).toNat := himp _ _ (hp11 14)
        have b22150 := hb (x 14 3)
        have b22151 := hb (x 14 11)
        clear * - r22149 b22150 b22151 d22140
        omega
      have d22152 : (x 12 3 && x 12 13).toNat = 0 := by
        have r22153 := hand1 (x 12 3) (x 12 13)
        have b22154 := hb (x 12 3)
        have b22155 := hb (x 12 3 && x 12 13)
        clear * - r22153 b22154 b22155 d22056
        omega
      have d22156 : (x 15 10).toNat = 1 := by
        have r22157 : 1 ≤ (x 15 10).toNat + (x 14 1 && x 14 11).toNat + (x 13 2 && x 13 12).toNat + (x 12 3 && x 12 13).toNat + (x 11 4 && x 11 14).toNat + (x 10 5).toNat := by have q := hcov10 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22158 := hb (x 10 5)
        have b22159 := hb (x 15 10)
        have b22160 := hb (x 14 1 && x 14 11)
        have b22161 := hb (x 13 2 && x 13 12)
        have b22162 := hb (x 12 3 && x 12 13)
        have b22163 := hb (x 11 4 && x 11 14)
        clear * - r22157 b22158 b22159 b22160 b22161 b22162 b22163 d21963 d21991 d22152 d21895 d21903
        omega
      have d22164 : (x 17 8).toNat = 0 := by
        have r22165 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22166 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
        have e22167 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
        have e22168 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
        have e22169 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
        have e22170 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
        have e22171 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
        have b22172 := hb (x 10 7)
        have b22173 := hb (x 11 6)
        have b22174 := hb (x 12 5)
        have b22175 := hb (x 13 4)
        have b22176 := hb (x 14 11)
        have b22177 := hb (x 15 10)
        have b22178 := hb (x 16 9)
        have b22179 := hb (x 17 8)
        clear * - r22165 e22166 e22167 e22168 e22169 e22170 e22171 b22172 b22173 b22174 b22175 b22176 b22177 b22178 b22179 d22156 d22148
        omega
      have d22180 : (x 16 9).toNat = 0 := by
        have r22181 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22182 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
        have e22183 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
        have e22184 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
        have e22185 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
        have e22186 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
        have e22187 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
        have b22188 := hb (x 10 7)
        have b22189 := hb (x 11 6)
        have b22190 := hb (x 12 5)
        have b22191 := hb (x 13 4)
        have b22192 := hb (x 14 11)
        have b22193 := hb (x 15 10)
        have b22194 := hb (x 16 9)
        have b22195 := hb (x 17 8)
        clear * - r22181 e22182 e22183 e22184 e22185 e22186 e22187 b22188 b22189 b22190 b22191 b22192 b22193 b22194 b22195 d22164 d22156 d22148
        omega
      have d22196 : (x 13 4).toNat = 0 := by
        have r22197 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22198 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
        have e22199 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
        have e22200 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
        have e22201 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
        have e22202 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
        have e22203 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
        have b22204 := hb (x 10 7)
        have b22205 := hb (x 11 6)
        have b22206 := hb (x 12 5)
        have b22207 := hb (x 13 4)
        have b22208 := hb (x 14 11)
        have b22209 := hb (x 15 10)
        have b22210 := hb (x 16 9)
        have b22211 := hb (x 17 8)
        clear * - r22197 e22198 e22199 e22200 e22201 e22202 e22203 b22204 b22205 b22206 b22207 b22208 b22209 b22210 b22211 d22164 d22180 d22156 d22148
        omega
      have d22212 : (x 12 5).toNat = 0 := by
        have r22213 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22214 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
        have e22215 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
        have e22216 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
        have e22217 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
        have e22218 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
        have e22219 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
        have b22220 := hb (x 10 7)
        have b22221 := hb (x 11 6)
        have b22222 := hb (x 12 5)
        have b22223 := hb (x 13 4)
        have b22224 := hb (x 14 11)
        have b22225 := hb (x 15 10)
        have b22226 := hb (x 16 9)
        have b22227 := hb (x 17 8)
        clear * - r22213 e22214 e22215 e22216 e22217 e22218 e22219 b22220 b22221 b22222 b22223 b22224 b22225 b22226 b22227 d22164 d22180 d22156 d22148 d22196
        omega
      have d22228 : (x 11 6).toNat = 0 := by
        have r22229 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22230 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
        have e22231 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
        have e22232 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
        have e22233 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
        have e22234 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
        have e22235 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
        have b22236 := hb (x 10 7)
        have b22237 := hb (x 11 6)
        have b22238 := hb (x 12 5)
        have b22239 := hb (x 13 4)
        have b22240 := hb (x 14 11)
        have b22241 := hb (x 15 10)
        have b22242 := hb (x 16 9)
        have b22243 := hb (x 17 8)
        clear * - r22229 e22230 e22231 e22232 e22233 e22234 e22235 b22236 b22237 b22238 b22239 b22240 b22241 b22242 b22243 d22164 d22180 d22156 d22148 d22196 d22212
        omega
      have d22244 : (x 10 7).toNat = 0 := by
        have r22245 : (x 17 8).toNat + (x 16 1 && x 16 9).toNat + (x 15 2 && x 15 10).toNat + (x 14 3 && x 14 11).toNat + (x 13 4 && x 13 12).toNat + (x 12 5 && x 12 13).toNat + (x 11 6 && x 11 14).toNat + (x 10 7).toNat = 1 := by have q := hd8 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22246 : (x 16 1 && x 16 9).toNat = (x 16 9).toNat := handr _ _ (fun h => hp9 16 (h))
        have e22247 : (x 15 2 && x 15 10).toNat = (x 15 10).toNat := handr _ _ (fun h => hp10 15 (h))
        have e22248 : (x 14 3 && x 14 11).toNat = (x 14 11).toNat := handr _ _ (fun h => hp11 14 (h))
        have e22249 : (x 13 4 && x 13 12).toNat = (x 13 4).toNat := handl _ _ (fun h => hp4 13 (h))
        have e22250 : (x 12 5 && x 12 13).toNat = (x 12 5).toNat := handl _ _ (fun h => hp5 12 (h))
        have e22251 : (x 11 6 && x 11 14).toNat = (x 11 6).toNat := handl _ _ (fun h => hp6 11 (h))
        have b22252 := hb (x 10 7)
        have b22253 := hb (x 11 6)
        have b22254 := hb (x 12 5)
        have b22255 := hb (x 13 4)
        have b22256 := hb (x 14 11)
        have b22257 := hb (x 15 10)
        have b22258 := hb (x 16 9)
        have b22259 := hb (x 17 8)
        clear * - r22245 e22246 e22247 e22248 e22249 e22250 e22251 b22252 b22253 b22254 b22255 b22256 b22257 b22258 b22259 d22164 d22180 d22156 d22148 d22196 d22212 d22228
        omega
      have d22260 : (x 12 3 && x 12 12).toNat = 0 := by
        have r22261 := hand1 (x 12 3) (x 12 12)
        have b22262 := hb (x 12 3)
        have b22263 := hb (x 12 3 && x 12 12)
        clear * - r22261 b22262 b22263 d22056
        omega
      have d22264 : (x 15 9).toNat = 1 := by
        have r22265 : 1 ≤ (x 15 9).toNat + (x 14 1 && x 14 10).toNat + (x 13 2 && x 13 11).toNat + (x 12 3 && x 12 12).toNat + (x 11 4 && x 11 13).toNat + (x 10 5 && x 10 14).toNat + (x 9 6).toNat := by have q := hcov9 15; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22266 := hb (x 9 6)
        have b22267 := hb (x 15 9)
        have b22268 := hb (x 14 1 && x 14 10)
        have b22269 := hb (x 13 2 && x 13 11)
        have b22270 := hb (x 12 3 && x 12 12)
        have b22271 := hb (x 11 4 && x 11 13)
        have b22272 := hb (x 10 5 && x 10 14)
        clear * - r22265 b22266 b22267 b22268 b22269 b22270 b22271 b22272 d21967 d21995 d22260 d21899 d21919 d21923
        omega
      have d22273 : (x 16 8).toNat = 0 := by
        have r22274 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22275 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e22276 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e22277 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e22278 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e22279 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e22280 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have b22281 := hb (x 9 7)
        have b22282 := hb (x 10 6)
        have b22283 := hb (x 11 5)
        have b22284 := hb (x 12 4)
        have b22285 := hb (x 13 11)
        have b22286 := hb (x 14 10)
        have b22287 := hb (x 15 9)
        have b22288 := hb (x 16 8)
        clear * - r22274 e22275 e22276 e22277 e22278 e22279 e22280 b22281 b22282 b22283 b22284 b22285 b22286 b22287 b22288 d22264 d22040 d22052
        omega
      have d22289 : (x 12 4).toNat = 0 := by
        have r22290 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22291 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e22292 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e22293 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e22294 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e22295 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e22296 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have b22297 := hb (x 9 7)
        have b22298 := hb (x 10 6)
        have b22299 := hb (x 11 5)
        have b22300 := hb (x 12 4)
        have b22301 := hb (x 13 11)
        have b22302 := hb (x 14 10)
        have b22303 := hb (x 15 9)
        have b22304 := hb (x 16 8)
        clear * - r22290 e22291 e22292 e22293 e22294 e22295 e22296 b22297 b22298 b22299 b22300 b22301 b22302 b22303 b22304 d22273 d22264 d22040 d22052
        omega
      have d22305 : (x 11 5).toNat = 0 := by
        have r22306 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22307 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e22308 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e22309 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e22310 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e22311 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e22312 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have b22313 := hb (x 9 7)
        have b22314 := hb (x 10 6)
        have b22315 := hb (x 11 5)
        have b22316 := hb (x 12 4)
        have b22317 := hb (x 13 11)
        have b22318 := hb (x 14 10)
        have b22319 := hb (x 15 9)
        have b22320 := hb (x 16 8)
        clear * - r22306 e22307 e22308 e22309 e22310 e22311 e22312 b22313 b22314 b22315 b22316 b22317 b22318 b22319 b22320 d22273 d22264 d22040 d22052 d22289
        omega
      have d22321 : (x 11 5 && x 11 12).toNat = 0 := by
        have r22322 := hand1 (x 11 5) (x 11 12)
        have b22323 := hb (x 11 5)
        have b22324 := hb (x 11 5 && x 11 12)
        clear * - r22322 b22323 b22324 d22305
        omega
      have d22325 : (x 10 6).toNat = 0 := by
        have r22326 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22327 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e22328 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e22329 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e22330 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e22331 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e22332 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have b22333 := hb (x 9 7)
        have b22334 := hb (x 10 6)
        have b22335 := hb (x 11 5)
        have b22336 := hb (x 12 4)
        have b22337 := hb (x 13 11)
        have b22338 := hb (x 14 10)
        have b22339 := hb (x 15 9)
        have b22340 := hb (x 16 8)
        clear * - r22326 e22327 e22328 e22329 e22330 e22331 e22332 b22333 b22334 b22335 b22336 b22337 b22338 b22339 b22340 d22273 d22264 d22040 d22052 d22289 d22305
        omega
      have d22341 : (x 10 6 && x 10 13).toNat = 0 := by
        have r22342 := hand1 (x 10 6) (x 10 13)
        have b22343 := hb (x 10 6)
        have b22344 := hb (x 10 6 && x 10 13)
        clear * - r22342 b22343 b22344 d22325
        omega
      have d22345 : (x 9 7).toNat = 0 := by
        have r22346 : (x 16 8).toNat + (x 15 1 && x 15 9).toNat + (x 14 2 && x 14 10).toNat + (x 13 3 && x 13 11).toNat + (x 12 4 && x 12 12).toNat + (x 11 5 && x 11 13).toNat + (x 10 6 && x 10 14).toNat + (x 9 7).toNat = 1 := by have q := hd8 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22347 : (x 15 1 && x 15 9).toNat = (x 15 9).toNat := handr _ _ (fun h => hp9 15 (h))
        have e22348 : (x 14 2 && x 14 10).toNat = (x 14 10).toNat := handr _ _ (fun h => hp10 14 (h))
        have e22349 : (x 13 3 && x 13 11).toNat = (x 13 11).toNat := handr _ _ (fun h => hp11 13 (h))
        have e22350 : (x 12 4 && x 12 12).toNat = (x 12 4).toNat := handl _ _ (fun h => hp4 12 (h))
        have e22351 : (x 11 5 && x 11 13).toNat = (x 11 5).toNat := handl _ _ (fun h => hp5 11 (h))
        have e22352 : (x 10 6 && x 10 14).toNat = (x 10 6).toNat := handl _ _ (fun h => hp6 10 (h))
        have b22353 := hb (x 9 7)
        have b22354 := hb (x 10 6)
        have b22355 := hb (x 11 5)
        have b22356 := hb (x 12 4)
        have b22357 := hb (x 13 11)
        have b22358 := hb (x 14 10)
        have b22359 := hb (x 15 9)
        have b22360 := hb (x 16 8)
        clear * - r22346 e22347 e22348 e22349 e22350 e22351 e22352 b22353 b22354 b22355 b22356 b22357 b22358 b22359 b22360 d22273 d22264 d22040 d22052 d22289 d22305 d22325
        omega
      have d22361 : (x 9 7 && x 9 14).toNat = 0 := by
        have r22362 := hand1 (x 9 7) (x 9 14)
        have b22363 := hb (x 9 7)
        have b22364 := hb (x 9 7 && x 9 14)
        clear * - r22362 b22363 b22364 d22345
        omega
      have r22365 : (x 16 1).toNat + (x 15 2).toNat + (x 14 3).toNat + (x 13 4).toNat + (x 12 5).toNat + (x 11 6).toNat + (x 10 7).toNat + (x 9 8).toNat + (x 8 9).toNat + (x 7 10).toNat + (x 6 11).toNat + (x 5 12).toNat + (x 4 13).toNat + (x 3 14).toNat = 3 := by have q := hcount 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r22366 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22367 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e22368 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e22369 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e22370 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e22371 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e22372 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have r22373 : (x 9 8).toNat + (x 8 1 && x 8 9).toNat + (x 7 2 && x 7 10).toNat + (x 6 3 && x 6 11).toNat + (x 5 4 && x 5 12).toNat + (x 4 5 && x 4 13).toNat + (x 3 6 && x 3 14).toNat + (x 2 7).toNat = 1 := by have q := hd8 9; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22374 : (x 8 1 && x 8 9).toNat = (x 8 9).toNat := handr _ _ (fun h => hp9 8 (h))
      have e22375 : (x 7 2 && x 7 10).toNat = (x 7 10).toNat := handr _ _ (fun h => hp10 7 (h))
      have e22376 : (x 6 3 && x 6 11).toNat = (x 6 11).toNat := handr _ _ (fun h => hp11 6 (h))
      have e22377 : (x 5 4 && x 5 12).toNat = (x 5 4).toNat := handl _ _ (fun h => hp4 5 (h))
      have e22378 : (x 4 5 && x 4 13).toNat = (x 4 5).toNat := handl _ _ (fun h => hp5 4 (h))
      have e22379 : (x 3 6 && x 3 14).toNat = (x 3 6).toNat := handl _ _ (fun h => hp6 3 (h))
      have r22380 : (x 23 8).toNat + (x 22 1 && x 22 9).toNat + (x 21 2 && x 21 10).toNat + (x 20 3 && x 20 11).toNat + (x 19 4 && x 19 12).toNat + (x 18 5 && x 18 13).toNat + (x 17 6 && x 17 14).toNat + (x 16 7).toNat = 1 := by have q := hd8 23; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22381 : (x 22 1 && x 22 9).toNat = (x 22 9).toNat := handr _ _ (fun h => hp9 22 (h))
      have e22382 : (x 21 2 && x 21 10).toNat = (x 21 10).toNat := handr _ _ (fun h => hp10 21 (h))
      have e22383 : (x 20 3 && x 20 11).toNat = (x 20 11).toNat := handr _ _ (fun h => hp11 20 (h))
      have e22384 : (x 19 4 && x 19 12).toNat = (x 19 4).toNat := handl _ _ (fun h => hp4 19 (h))
      have e22385 : (x 18 5 && x 18 13).toNat = (x 18 5).toNat := handl _ _ (fun h => hp5 18 (h))
      have e22386 : (x 17 6 && x 17 14).toNat = (x 17 6).toNat := handl _ _ (fun h => hp6 17 (h))
      have r22387 : (x 19 12).toNat + (x 18 1 && x 18 13).toNat + (x 17 2 && x 17 14).toNat + (x 16 3).toNat = 1 := by have q := hd12 19; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22388 : (x 18 1 && x 18 13).toNat = (x 18 13).toNat := handr _ _ (fun h => hp13 18 (h))
      have e22389 : (x 17 2 && x 17 14).toNat = (x 17 2).toNat := handl _ _ (fun h => hp2 17 (h))
      have r22390 : (x 17 14).toNat + (x 16 1).toNat = 1 := by have q := hd14 17; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r22391 : 1 ≤ (x 16 7).toNat + (x 15 1 && x 15 8).toNat + (x 14 2 && x 14 9).toNat + (x 13 3 && x 13 10).toNat + (x 12 4 && x 12 11).toNat + (x 11 5 && x 11 12).toNat + (x 10 6 && x 10 13).toNat + (x 9 7 && x 9 14).toNat + (x 8 8).toNat := by have q := hcov7 16; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r22392 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r22393 : 1 ≤ (x 22 9).toNat + (x 21 1 && x 21 10).toNat + (x 20 2 && x 20 11).toNat + (x 19 3 && x 19 12).toNat + (x 18 4 && x 18 13).toNat + (x 17 5 && x 17 14).toNat + (x 16 6).toNat := by have q := hcov9 22; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r22394 : 1 ≤ (x 18 13).toNat + (x 17 1 && x 17 14).toNat + (x 16 2).toNat := by have q := hcov13 18; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have r22395 := hand2 (x 6 1) (x 6 10)
      have r22396 := hand2 (x 5 2) (x 5 11)
      have r22397 := hand2 (x 21 1) (x 21 10)
      have r22398 := hand2 (x 20 2) (x 20 11)
      have r22399 := hand2 (x 19 3) (x 19 12)
      have r22400 := hand2 (x 17 1) (x 17 14)
      linarith only [r22365, r22366, e22367, e22368, e22369, e22370, e22371, e22372, r22373, e22374, e22375, e22376, e22377, e22378, e22379, r22380, e22381, e22382, e22383, e22384, e22385, e22386, r22387, e22388, e22389, r22390, r22391, r22392, r22393, r22394, r22395, r22396, r22397, r22398, r22399, r22400, d21760, f21777, f21783, d21736, g7, g9, d21720, d21699, d21691, d21687, d21679, d22244, d22228, d22212, d22196, d22140, d22119, d22020, d22016, d21815, d21835, d21855, d21875, d22321, d22341, d22361, d21716, g11, d21756, d22099, d22115]
    · have f22461 : (x 2 6).toNat = 1 := by rw [h21782]; rfl
      have d22462 : (x 8 8).toNat = 0 := by
        have r22463 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22464 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e22465 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e22466 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e22467 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e22468 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e22469 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b22470 := hb (x 1 7)
        have b22471 := hb (x 2 6)
        have b22472 := hb (x 3 5)
        have b22473 := hb (x 4 4)
        have b22474 := hb (x 5 11)
        have b22475 := hb (x 6 10)
        have b22476 := hb (x 7 9)
        have b22477 := hb (x 8 8)
        clear * - r22463 e22464 e22465 e22466 e22467 e22468 e22469 b22470 b22471 b22472 b22473 b22474 b22475 b22476 b22477 d21720 d21736 f22461 f21777
        omega
      have d22478 : (x 7 9).toNat = 0 := by
        have r22479 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22480 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e22481 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e22482 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e22483 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e22484 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e22485 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b22486 := hb (x 1 7)
        have b22487 := hb (x 2 6)
        have b22488 := hb (x 3 5)
        have b22489 := hb (x 4 4)
        have b22490 := hb (x 5 11)
        have b22491 := hb (x 6 10)
        have b22492 := hb (x 7 9)
        have b22493 := hb (x 8 8)
        clear * - r22479 e22480 e22481 e22482 e22483 e22484 e22485 b22486 b22487 b22488 b22489 b22490 b22491 b22492 b22493 d22462 d21720 d21736 f22461 f21777
        omega
      have d22494 : (x 6 10).toNat = 0 := by
        have r22495 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have e22496 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
        have e22497 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
        have e22498 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
        have e22499 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
        have e22500 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
        have e22501 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
        have b22502 := hb (x 1 7)
        have b22503 := hb (x 2 6)
        have b22504 := hb (x 3 5)
        have b22505 := hb (x 4 4)
        have b22506 := hb (x 5 11)
        have b22507 := hb (x 6 10)
        have b22508 := hb (x 7 9)
        have b22509 := hb (x 8 8)
        clear * - r22495 e22496 e22497 e22498 e22499 e22500 e22501 b22502 b22503 b22504 b22505 b22506 b22507 b22508 b22509 d22462 d22478 d21720 d21736 f22461 f21777
        omega
      have d22510 : (x 6 1 && x 6 10).toNat = 0 := by
        have r22511 := hand2 (x 6 1) (x 6 10)
        have b22512 := hb (x 6 10)
        have b22513 := hb (x 6 1 && x 6 10)
        clear * - r22511 b22512 b22513 d22494
        omega
      have d22514 : (x 5 2 && x 5 11).toNat = 1 := by
        have r22515 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
        have b22516 := hb (x 1 6)
        have b22517 := hb (x 7 9)
        have b22518 := hb (x 6 1 && x 6 10)
        have b22519 := hb (x 5 2 && x 5 11)
        have b22520 := hb (x 4 3 && x 4 12)
        have b22521 := hb (x 3 4 && x 3 13)
        have b22522 := hb (x 2 5 && x 2 14)
        clear * - r22515 b22516 b22517 b22518 b22519 b22520 b22521 b22522 d22478 d22510 d21716 g11 d21756 d21760
        omega
      have d22523 : (x 5 11).toNat = 1 := by
        have r22524 := hand2 (x 5 2) (x 5 11)
        have b22525 := hb (x 5 11)
        have b22526 := hb (x 5 2 && x 5 11)
        clear * - r22524 b22525 b22526 d22514
        omega
      have r22527 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22528 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e22529 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e22530 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e22531 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e22532 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e22533 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b22534 := hb (x 1 7)
      have b22535 := hb (x 2 6)
      have b22536 := hb (x 3 5)
      have b22537 := hb (x 4 4)
      have b22538 := hb (x 5 11)
      have b22539 := hb (x 6 10)
      have b22540 := hb (x 7 9)
      have b22541 := hb (x 8 8)
      linarith only [r22527, e22528, e22529, e22530, e22531, e22532, e22533, b22534, b22535, b22536, b22537, b22538, b22539, b22540, b22541, d22462, d22478, d22494, d22523, d21720, d21736, f22461, f21777]
  · have f22542 : (x 1 7).toNat = 1 := by rw [h21776]; rfl
    have d22543 : (x 8 8).toNat = 0 := by
      have r22544 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22545 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e22546 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e22547 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e22548 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e22549 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e22550 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b22551 := hb (x 1 7)
      have b22552 := hb (x 2 6)
      have b22553 := hb (x 3 5)
      have b22554 := hb (x 4 4)
      have b22555 := hb (x 5 11)
      have b22556 := hb (x 6 10)
      have b22557 := hb (x 7 9)
      have b22558 := hb (x 8 8)
      clear * - r22544 e22545 e22546 e22547 e22548 e22549 e22550 b22551 b22552 b22553 b22554 b22555 b22556 b22557 b22558 d21720 d21736 f22542
      omega
    have d22559 : (x 7 9).toNat = 0 := by
      have r22560 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22561 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e22562 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e22563 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e22564 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e22565 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e22566 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b22567 := hb (x 1 7)
      have b22568 := hb (x 2 6)
      have b22569 := hb (x 3 5)
      have b22570 := hb (x 4 4)
      have b22571 := hb (x 5 11)
      have b22572 := hb (x 6 10)
      have b22573 := hb (x 7 9)
      have b22574 := hb (x 8 8)
      clear * - r22560 e22561 e22562 e22563 e22564 e22565 e22566 b22567 b22568 b22569 b22570 b22571 b22572 b22573 b22574 d22543 d21720 d21736 f22542
      omega
    have d22575 : (x 6 10).toNat = 0 := by
      have r22576 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have e22577 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
      have e22578 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
      have e22579 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
      have e22580 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
      have e22581 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
      have e22582 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
      have b22583 := hb (x 1 7)
      have b22584 := hb (x 2 6)
      have b22585 := hb (x 3 5)
      have b22586 := hb (x 4 4)
      have b22587 := hb (x 5 11)
      have b22588 := hb (x 6 10)
      have b22589 := hb (x 7 9)
      have b22590 := hb (x 8 8)
      clear * - r22576 e22577 e22578 e22579 e22580 e22581 e22582 b22583 b22584 b22585 b22586 b22587 b22588 b22589 b22590 d22543 d22559 d21720 d21736 f22542
      omega
    have d22591 : (x 6 1 && x 6 10).toNat = 0 := by
      have r22592 := hand2 (x 6 1) (x 6 10)
      have b22593 := hb (x 6 10)
      have b22594 := hb (x 6 1 && x 6 10)
      clear * - r22592 b22593 b22594 d22575
      omega
    have d22595 : (x 5 2 && x 5 11).toNat = 1 := by
      have r22596 : 1 ≤ (x 7 9).toNat + (x 6 1 && x 6 10).toNat + (x 5 2 && x 5 11).toNat + (x 4 3 && x 4 12).toNat + (x 3 4 && x 3 13).toNat + (x 2 5 && x 2 14).toNat + (x 1 6).toNat := by have q := hcov9 7; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
      have b22597 := hb (x 1 6)
      have b22598 := hb (x 7 9)
      have b22599 := hb (x 6 1 && x 6 10)
      have b22600 := hb (x 5 2 && x 5 11)
      have b22601 := hb (x 4 3 && x 4 12)
      have b22602 := hb (x 3 4 && x 3 13)
      have b22603 := hb (x 2 5 && x 2 14)
      clear * - r22596 b22597 b22598 b22599 b22600 b22601 b22602 b22603 d22559 d22591 d21716 g11 d21756 d21760
      omega
    have d22604 : (x 5 11).toNat = 1 := by
      have r22605 := hand2 (x 5 2) (x 5 11)
      have b22606 := hb (x 5 11)
      have b22607 := hb (x 5 2 && x 5 11)
      clear * - r22605 b22606 b22607 d22595
      omega
    have r22608 : (x 8 8).toNat + (x 7 1 && x 7 9).toNat + (x 6 2 && x 6 10).toNat + (x 5 3 && x 5 11).toNat + (x 4 4 && x 4 12).toNat + (x 3 5 && x 3 13).toNat + (x 2 6 && x 2 14).toNat + (x 1 7).toNat = 1 := by have q := hd8 8; simp only [Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at q; exact q
    have e22609 : (x 7 1 && x 7 9).toNat = (x 7 9).toNat := handr _ _ (fun h => hp9 7 (h))
    have e22610 : (x 6 2 && x 6 10).toNat = (x 6 10).toNat := handr _ _ (fun h => hp10 6 (h))
    have e22611 : (x 5 3 && x 5 11).toNat = (x 5 11).toNat := handr _ _ (fun h => hp11 5 (h))
    have e22612 : (x 4 4 && x 4 12).toNat = (x 4 4).toNat := handl _ _ (fun h => hp4 4 (h))
    have e22613 : (x 3 5 && x 3 13).toNat = (x 3 5).toNat := handl _ _ (fun h => hp5 3 (h))
    have e22614 : (x 2 6 && x 2 14).toNat = (x 2 6).toNat := handl _ _ (fun h => hp6 2 (h))
    have b22615 := hb (x 1 7)
    have b22616 := hb (x 2 6)
    have b22617 := hb (x 3 5)
    have b22618 := hb (x 4 4)
    have b22619 := hb (x 5 11)
    have b22620 := hb (x 6 10)
    have b22621 := hb (x 7 9)
    have b22622 := hb (x 8 8)
    linarith only [r22608, e22609, e22610, e22611, e22612, e22613, e22614, b22615, b22616, b22617, b22618, b22619, b22620, b22621, b22622, d22543, d22559, d22575, d22604, d21720, d21736, f22542]

theorem cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00001 (x : ℤ → Fin 16 → Bool)
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
    (g0 : (x 0 5).toNat = 0)
    (g1 : (x 0 7).toNat = 1)
    (g2 : (x 0 8).toNat = 0)
    (g3 : (x 1 14).toNat = 1)
    (g4 : (x 2 13).toNat = 1)
    (g5 : (x 3 2).toNat = 0)
    (g6 : (x 3 4).toNat = 0)
    (g7 : (x 3 6).toNat = 0)
    (g8 : (x 3 12).toNat = 0)
    (g9 : (x 3 14).toNat = 0)
    (g10 : (x 3 5 && x 3 12).toNat = 0)
    (g11 : (x 3 4 && x 3 13).toNat = 0)
    (g12 : (x 3 2 && x 3 12).toNat = 0)
    (g13 : (x 1 4 && x 1 14).toNat = 0)
    (g14 : (x 3 1 && x 3 14).toNat = 0)
    : False := cycle_power_fifteen_tight_type_sequence_one_alternates_core_alt00001_aux x hcount hd14 hd12 hd8 hcov1 hcov2 hcov3 hcov4 hcov5 hcov6 hcov7 hcov9 hcov10 hcov11 hcov13 hp2 hp4 hp5 hp6 hp9 hp10 hp11 hp13 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14
