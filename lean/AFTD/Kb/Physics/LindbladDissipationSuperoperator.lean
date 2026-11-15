import AFTD.Prelude

/-!
# lindblad_dissipation_superoperator

Topic: quantum_mechanics   Node: bd3a875d849e

Provenance: formalization of a published result. Source: arXiv:2610.37187

The positive dissipation superoperator -L(X) = 1/2 sum_j [J_j, [J_j, X]] for a family of Hermitian jump operators J_j.
-/

/-- The positive superoperator -L for a purely dissipative Lindblad generator with Hermitian jump operators. -/
noncomputable def lindblad_dissipation_superoperator {ι : Type*} [Fintype ι] {d : ℕ}
    (J : ι → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  (1 / 2 : ℂ) • ∑ j,
    ((LinearMap.mulLeft ℂ (J j) - LinearMap.mulRight ℂ (J j)).comp
      (LinearMap.mulLeft ℂ (J j) - LinearMap.mulRight ℂ (J j)))
