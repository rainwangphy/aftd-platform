import AFTD.Prelude
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.PauliMatrix
import AFTD.Kb.Tcs.InstFintypePauliString

/-!
# pauli_choi_matrix

Topic: quantum   Node: 2fa6283e6a41

Provenance: formalization of a published result. Source: arXiv:2611.34872, Eq. (17)

Given an implicit natural number n and an error distribution p : PauliString n → ℝ, pauli_choi_matrix p is the bipartite Choi matrix with row (i₁, j₁) and column (i₂, j₂) entry given by (1 / (2 : ℂ)^n) * ∑_P (p P : ℂ) * (pauliMatrix P i₁ j₁) * star (pauliMatrix P i₂ j₂), representing the mixture of Bell projectors.
-/

/-- The Choi matrix of an n-qubit Pauli channel with error rates p. -/
noncomputable def pauli_choi_matrix {n : ℕ} (p : PauliString n → ℝ) :
    Matrix ((Fin n → Fin 2) × (Fin n → Fin 2)) ((Fin n → Fin 2) × (Fin n → Fin 2)) ℂ :=
  Matrix.of fun (i₁, j₁) (i₂, j₂) =>
    (1 / (2 : ℂ)^n) * ∑ P : PauliString n, (p P : ℂ) * (pauliMatrix P i₁ j₁) * star (pauliMatrix P i₂ j₂)
