import AFTD.Prelude
import AFTD.Kb.Optimization.IsWolfeCorral
import AFTD.Kb.Optimization.IsAffineMinimizer

/-!
# wolfe_minor_step

Topic: submodular   Node: 9efffc020d64

Provenance: formalization of a published result. Source: arXiv:2611.12680 Sec. 2.2 Algorithm 2

For states (T, lam) and (T', lam') in Finset (Fin n → ℝ) × ((Fin n → ℝ) → ℝ), wolfe_minor_step asserts that T is not a Wolfe corral, and there exist an affine minimizer μ of T with center w, a step size θ with 0 ≤ θ ≤ 1, and an atom p_drop ∈ T such that (1 - θ) * lam p + θ * μ p ≥ 0 for all p ∈ T, μ(p_drop) < lam(p_drop) with (1 - θ) * lam(p_drop) + θ * μ(p_drop) = 0, lam' = (fun p => (1 - θ) * lam p + θ * μ p), and T' = T.erase p_drop.
-/

/-- A single minor cycle step of Wolfe's method moving convex combination weights to the boundary. -/
def wolfe_minor_step {n : ℕ}
    (state state' : Finset (Fin n → ℝ) × ((Fin n → ℝ) → ℝ)) : Prop :=
  let (T, lam) := state
  let (T', lam') := state'
  (¬ ∃ w, is_wolfe_corral T w) ∧
  ∃ (w : Fin n → ℝ) (μ : (Fin n → ℝ) → ℝ) (θ : ℝ) (p_drop : Fin n → ℝ),
    is_affine_minimizer T w μ ∧
    0 ≤ θ ∧ θ ≤ 1 ∧
    (∀ p ∈ T, 0 ≤ (1 - θ) * lam p + θ * μ p) ∧
    p_drop ∈ T ∧ μ p_drop < lam p_drop ∧
    (1 - θ) * lam p_drop + θ * μ p_drop = 0 ∧
    lam' = (fun p => (1 - θ) * lam p + θ * μ p) ∧
    T' = T.erase p_drop
