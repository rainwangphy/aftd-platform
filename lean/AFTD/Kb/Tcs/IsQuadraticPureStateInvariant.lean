import AFTD.Prelude
import AFTD.Kb.Tcs.IsPureState
import AFTD.Kb.Tcs.QuadraticPureStateForm

/-!
# is_quadratic_pure_state_invariant

Topic: quantum   Node: c8c9e1762a23

Provenance: formalization of a published result. Source: arXiv:2610.36076 Def. 1

A weight vector zeta : Fin (d^2 - 1) → ℝ is a quadratic pure-state invariant for T if there exists a real constant c such that for all matrices rho with is_pure_state rho, quadratic_pure_state_form T zeta rho = c.
-/

/-- A weight vector zeta is a quadratic pure-state invariant if the quadratic form I_rho(zeta) is constant across all pure quantum states rho. -/
def is_quadratic_pure_state_invariant {d : ℕ} (T : Fin (d^2 - 1) → Matrix (Fin d) (Fin d) ℂ)
    (ζ : Fin (d^2 - 1) → ℝ) : Prop := ∃ c : ℝ, ∀ ρ : Matrix (Fin d) (Fin d) ℂ, is_pure_state ρ → quadratic_pure_state_form T ζ ρ = c
