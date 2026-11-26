import AFTD.Prelude
import AFTD.Kb.Tcs.IsSignedPauli

/-!
# is_pure_stabilizer_state

Topic: quantum   Node: d80c8aaf3a39

Provenance: formalization of a published result. Source: Gottesman 1997; arXiv:2611.34872, lines 166, 196

A pure $n$-qubit stabilizer state is the rank-$1$ projection $(1/2^n) \sum_{g \in S} g$ for an abelian subgroup $S$ of $2^n$ signed Pauli operators not containing $-I$.
-/

open scoped BigOperators in
/-- A pure n-qubit stabilizer state is the rank-1 projection onto the joint +1 eigenspace of an abelian subgroup of 2^n signed Paulis not containing -I. -/
def is_pure_stabilizer_state {n : ℕ} (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : Prop := ∃ S : Finset (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
    S.card = 2^n ∧
    (∀ A ∈ S, is_signed_pauli A) ∧
    (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) ∈ S ∧
    (-1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) ∉ S ∧
    (∀ A ∈ S, ∀ B ∈ S, A * B ∈ S) ∧
    ρ = ((1 : ℂ) / (2 : ℂ)^n) • ∑ A ∈ S, A
