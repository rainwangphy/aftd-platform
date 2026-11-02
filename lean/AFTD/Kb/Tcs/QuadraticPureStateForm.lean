import AFTD.Prelude

/-!
# quadratic_pure_state_form

Topic: quantum   Node: e2b22621a933

Provenance: formalization of a published result. Source: arXiv:2610.36076 Def. 1

For a family of matrices T, a weight vector zeta : Fin (d^2 - 1) → ℝ, and a density matrix rho, the quadratic pure-state form is the sum over a : Fin (d^2 - 1) of zeta a * (Matrix.trace (rho * T a)).re ^ 2.
-/

/-- The quadratic pure-state form I_rho(zeta) evaluates the sum over basis operators T_a of zeta_a times (Re(Tr(rho T_a)))^2. -/
def quadratic_pure_state_form {d : ℕ} (T : Fin (d^2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (ζ : Fin (d^2 - 1) → ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ := ∑ a : Fin (d^2 - 1), ζ a * ((Matrix.trace (ρ * T a)).re ^ 2)
