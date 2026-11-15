import AFTD.Prelude

/-!
# bessel_I0

Topic: quantum_mechanics   Node: 3854d8f557dd

Provenance: formalization of a published result. Source: arXiv:2611.17021

The real-valued modified Bessel function of the first kind of order zero is the function bessel_I0 : Real -> Real mapping a real number z to the infinite sum over all natural numbers j of (z^2 / 4)^j / ((Nat.factorial j : Real)^2).
-/

/-- The modified Bessel function of the first kind of order zero on the real numbers. -/
noncomputable def bessel_I0 (z : ℝ) : ℝ :=
  ∑' j : ℕ, (z ^ 2 / 4) ^ j / ((Nat.factorial j : ℝ) ^ 2)
