import AFTD.Prelude
import AFTD.Kb.Tcs.IsSeparableBipartite
import AFTD.Kb.Tcs.PauliChoiMatrix
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.InstFintypePauliString

/-!
# is_eb_pauli_channel

Topic: quantum   Node: ccf7fa937578

Provenance: formalization of a published result. Source: arXiv:2611.34872, Section II

A probability distribution p on n-qubit Pauli operators defines an entanglement-breaking Pauli channel if each p(P) ≥ 0, ∑_P p(P) = 1, and its Choi matrix pauli_choi_matrix p is separable.
-/

/-- An n-qubit Pauli channel is entanglement-breaking if its Choi state is separable. -/
def is_eb_pauli_channel {n : ℕ} (p : PauliString n → ℝ) : Prop :=
  (∀ P, 0 ≤ p P) ∧ (∑ P, p P = 1) ∧ is_separable_bipartite (pauli_choi_matrix p)
