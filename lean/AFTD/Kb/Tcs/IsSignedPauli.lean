import AFTD.Prelude
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.PauliMatrix

/-!
# is_signed_pauli

Topic: quantum   Node: d45b1992ab28

Provenance: formalization of a published result. Source: arXiv:2611.34872, line 151

A signed $n$-qubit Pauli operator is of the form $\pm P$ for an $n$-qubit Pauli string $P$.
-/

/-- A signed n-qubit Pauli operator is a Pauli matrix multiplied by +1 or -1. -/
def is_signed_pauli {n : ℕ} (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : Prop := ∃ (P : PauliString n) (s : ℂ), (s = 1 ∨ s = -1) ∧ A = s • pauliMatrix P
