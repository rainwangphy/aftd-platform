import AFTD.Prelude

/-!
# op874_four_squares_ownership_count_obstruction

Topic: graphs   Node: 7ed6db62b4fe

Provenance: helper lemma. Finite fixed-cut obstructions for OP-874, motivated by https://arxiv.org/abs/2610.41950 and experiments 41600–41607.

The matching-owner counts and required adjacent factor-edge covers in the four-square obstruction are inconsistent.
-/

theorem op874_four_squares_ownership_count_obstruction
    (m : Fin 16 → ℕ)
    (h13 : m 1 + m 3 = 1) (h913 : m 9 + m 13 = 1)
    (h25 : m 2 + m 5 = 1) (h06 : m 0 + m 6 = 1)
    (h1214 : m 12 + m 14 = 1)
    (h815 : m 8 + m 15 = 1) (h711 : m 7 + m 11 = 1)
    (h0 : m 0 + m 1 + m 2 + m 3 ≤ 2)
    (h3 : m 12 + m 13 + m 14 + m 15 ≤ 2)
    (hp : m 5 + m 6 + m 7 ≤ 1)
    (hq : m 8 + m 9 + m 11 ≤ 1) : False := by
  omega
