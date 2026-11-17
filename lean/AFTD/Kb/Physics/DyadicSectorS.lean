import AFTD.Prelude

/-!
# dyadic_sector_S

Topic: quantum_mechanics   Node: 37ffb0e4a361

Provenance: formalization of a published result. Source: arXiv:2611.07003; OP-1787

Given a natural number s and a real number t, let A = 2^s and B = A^2. The function dyadic_sector_S s t is defined by setting the integer j = ⌊Real.log (t * (B - 1)) / Real.log B⌋ and returning A^j / (A - 1) + (t - B^j / (B - 1)) * A^(-j).
-/

/-- Piecewise linear geometric sector amplitude function S(t) for dyadic phase envelopes. -/
noncomputable def dyadic_sector_S (s : ℕ) (t : ℝ) : ℝ :=
  let A : ℝ := (2 : ℝ) ^ s
  let B : ℝ := A ^ 2
  let j : ℤ := ⌊Real.log (t * (B - 1)) / Real.log B⌋
  A ^ j / (A - 1) + (t - B ^ j / (B - 1)) * A ^ (-j)
