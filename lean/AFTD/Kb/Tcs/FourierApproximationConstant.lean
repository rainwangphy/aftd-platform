import AFTD.Prelude

/-!
# fourier_approximation_constant

Topic: circuits   Node: b4719cf2517a

Provenance: formalization of a published result. Source: scout/2611-06451-fourier-entropy-bounds-via-approximations.md:813

For a real parameter a, the Fourier approximation constant K_a is defined as the infinite series ∑_{j=1}^∞ 2^(-j) (j+3)^a, indexed over positive integers j.
-/

/-- Fourier approximation constant K_a defined as the infinite series ∑_{j=1}^∞ 2^(-j) (j+3)^a. -/
noncomputable def fourier_approximation_constant (a : ℝ) : ℝ := ∑' j : ℕ+, (1 / 2 : ℝ) ^ (j : ℕ) * ((j : ℝ) + 3) ^ a
