import AFTD.Prelude

/-!
# dyadic_phase_envelope

Topic: quantum_mechanics   Node: 7711424ae128

Provenance: formalization of a published result. Source: arXiv:2611.07003; OP-1787

Given a natural number s and a real number t, let A = 2^s, B = A^2, and for real y let S(y) = A^j / (A - 1) + (y - B^j / (B - 1)) * A^(-j) with j = ⌊Real.log (y * (B - 1)) / Real.log B⌋. Then dyadic_phase_envelope s t is the maximum over k in Finset.range (2 * s) (starting at 0) of max (S(x)^2 / x) (max (A * S(x / A)^2 / x) ((S(x) + Real.sqrt A * S(x / A))^2 / (2 * x))) where x = (2 : ℝ)^k * t.
-/

/-- The dyadic phase envelope E_s(t) optimizing pure and balanced stabilizer sectors across dyadic scales. -/
noncomputable def dyadic_phase_envelope (s : ℕ) (t : ℝ) : ℝ :=
  let A : ℝ := (2 : ℝ) ^ s
  (Finset.range (2 * s)).fold max 0 (fun k =>
    let x : ℝ := (2 : ℝ) ^ k * t
    let sx : ℝ := S x
    let sxa : ℝ := S (x / A)
    max (sx ^ 2 / x) (max (A * sxa ^ 2 / x) ((sx + Real.sqrt A * sxa) ^ 2 / (2 * x))))
where
  S (x : ℝ) : ℝ :=
    let A : ℝ := (2 : ℝ) ^ s
    let B : ℝ := A ^ 2
    let j : ℤ := ⌊Real.log (x * (B - 1)) / Real.log B⌋
    A ^ j / (A - 1) + (x - B ^ j / (B - 1)) * A ^ (-j)
