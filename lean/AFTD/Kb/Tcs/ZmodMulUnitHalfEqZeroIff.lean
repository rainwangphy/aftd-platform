import AFTD.Prelude

/-!
# zmod_mul_unit_half_eq_zero_iff

Topic: combinatorics   Node: bfb16d8c53f1

Provenance: helper lemma. lemma for arXiv:2610.23958 Proposition 6.2 (PR-301)

In ZMod n, if 2u = 1 then x u = 0 iff x = 0.
-/

theorem zmod_mul_unit_half_eq_zero_iff {n : ℕ} {u : ZMod n} (hu : 2 * u = 1) (x : ZMod n) :
    x * u = 0 ↔ x = 0 := by
  constructor
  · intro hx
    calc x = x * (2 * u) := by rw [hu, mul_one]
      _ = 2 * (x * u) := by ring
      _ = 0 := by rw [hx, mul_zero]
  · intro hx; rw [hx, zero_mul]
