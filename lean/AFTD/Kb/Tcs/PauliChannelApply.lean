import AFTD.Prelude
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.PauliMatrix
import AFTD.Kb.Tcs.InstFintypePauliString

/-!
# pauli_channel_apply

Topic: quantum   Node: d9cd1ba49a00

Provenance: formalization of a published result. Source: arXiv:2611.34872

For an n-qubit Pauli probability distribution p and an n-qubit density matrix ρ, the Pauli channel maps ρ to ∑_P p(P) P ρ P.
-/

/-- Action of an n-qubit Pauli channel with probability vector p on an n-qubit state. -/
noncomputable def pauli_channel_apply {n : ℕ} (p : PauliString n → ℝ)
    (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ∑ P : PauliString n, (p P : ℂ) • (pauliMatrix P * ρ * pauliMatrix P)
