import AFTD.Prelude
import AFTD.Kb.Tcs.IsOrthonormalHermitianBasis
import AFTD.Kb.Tcs.IsPureState
import AFTD.Kb.Tcs.IsQuadraticPureStateInvariant
import AFTD.Kb.Tcs.QuadraticPureStateForm
import AFTD.Kb.Tcs.HermitianMatrixParsevalSum
import AFTD.Kb.Tcs.OrthonormalHermitianBasisBlochNormSq

/-!
# open_problem_qudit_pure_state_invariants

Topic: quantum   Node: 029146b2468c

Provenance: formalization of a published result. Source: arXiv:2610.36076 Sec. 6, lines 2765-2766

For any natural number d ≥ 3 and any family T of d^2 - 1 matrices satisfying is_orthonormal_hermitian_basis d T, the constant function (fun _ => 1) is a quadratic pure-state invariant for T, and for all matrices rho satisfying is_pure_state rho, quadratic_pure_state_form T (fun _ => 1) rho equals ((d : ℝ) - 1) / (d : ℝ).
-/

/-- For any qudit system of dimension d >= 3 and any orthonormal Hermitian operator basis T of su(d), the constant weight vector zeta = 1 is a quadratic pure-state invariant with value (d-1)/d on all pure states. -/
theorem open_problem_qudit_pure_state_invariants (d : ℕ) (hd : 3 ≤ d)
    (T : Fin (d^2 - 1) → Matrix (Fin d) (Fin d) ℂ) (hT : is_orthonormal_hermitian_basis d T) :
    is_quadratic_pure_state_invariant T (fun _ => 1) ∧
    ∀ ρ : Matrix (Fin d) (Fin d) ℂ, is_pure_state ρ →
      quadratic_pure_state_form T (fun _ => 1) ρ = ((d : ℝ) - 1) / (d : ℝ) := by
  refine ⟨⟨((d : ℝ) - 1) / (d : ℝ), ?_⟩, ?_⟩
  · intro ρ hρ
    exact orthonormal_hermitian_basis_bloch_norm_sq d (by omega) T hT ρ hρ
  · intro ρ hρ
    exact orthonormal_hermitian_basis_bloch_norm_sq d (by omega) T hT ρ hρ
