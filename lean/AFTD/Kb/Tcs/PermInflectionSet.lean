import AFTD.Prelude
import AFTD.Kb.Tcs.PermSecondDerivative

/-!
# perm_inflection_set

Topic: combinatorics   Node: 757f8ce8fd5f

Provenance: formalization of a published result. Source: arXiv:2610.38237, Definition 1.3

For a permutation σ : Equiv.Perm (Fin n), the inflection set perm_inflection_set σ : Finset (ℕ × ℕ) is the filter of pairs (m, p) in Finset.Icc 2 (n - 1) ×ˢ Finset.Icc 2 (n - 1) satisfying m < p, perm_second_derivative σ m * perm_second_derivative σ p < 0, and perm_second_derivative σ ℓ = 0 for all ℓ ∈ Finset.Ioo m p.
-/

/-- The set of pairs (m, p) of indices where permutation σ changes sign in its second derivative. -/
def perm_inflection_set {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (ℕ × ℕ) := (Finset.Icc 2 (n - 1) ×ˢ Finset.Icc 2 (n - 1)).filter fun ⟨m, p⟩ =>
    m < p ∧
    perm_second_derivative σ m * perm_second_derivative σ p < 0 ∧
    ∀ ℓ ∈ Finset.Ioo m p, perm_second_derivative σ ℓ = 0
