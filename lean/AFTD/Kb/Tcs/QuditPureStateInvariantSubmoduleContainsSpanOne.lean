import AFTD.Prelude
import AFTD.Kb.Tcs.QuadraticPureStateInvariantSubmodule
import AFTD.Kb.Tcs.OpenProblemQuditPureStateInvariants
import AFTD.Kb.Tcs.IsOrthonormalHermitianBasis
import AFTD.Kb.Tcs.IsQuadraticPureStateInvariant
import AFTD.Kb.Tcs.QuadraticPureStateForm
import AFTD.Kb.Tcs.IsPureState

/-!
# qudit_pure_state_invariant_submodule_contains_span_one

Topic: quantum   Node: def998cbd404

Provenance: formalization of a published result. Source: arXiv:2610.36076 Sec. 6

For any qudit dimension d ≥ 3 and any orthonormal Hermitian operator basis T of su(d), the submodule of quadratic pure-state invariants contains the one-dimensional subspace spanned by the all-ones weight vector.
-/

/-- The quadratic pure-state invariant submodule contains the span of the all-ones vector. -/
theorem qudit_pure_state_invariant_submodule_contains_span_one (d : ℕ) (hd : 3 ≤ d)
    (T : Fin (d^2 - 1) → Matrix (Fin d) (Fin d) ℂ) (hT : is_orthonormal_hermitian_basis d T) :
    Submodule.span ℝ {fun _ : Fin (d^2 - 1) => (1 : ℝ)} ≤ quadratic_pure_state_invariant_submodule T := by
  rw [Submodule.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (open_problem_qudit_pure_state_invariants d hd T hT).1
