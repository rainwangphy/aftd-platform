import AFTD.Prelude

/-!
# zonotope_generator

Topic: graphs   Node: 680966a0d26d

Provenance: formalization of a published result. Source: arXiv:2610.14100 eq. (4)

For natural numbers n and m, the m-th generator vector g_m in ℂ is (1/n)(1 - exp(-2πi m/n)).
-/

/-- The m-th generator of the zonotope polygon S_n for order n. -/
noncomputable def zonotope_generator (n : ℕ) (m : ℕ) : ℂ := (1 / (n : ℂ)) * (1 - Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) / (n : ℂ)))
