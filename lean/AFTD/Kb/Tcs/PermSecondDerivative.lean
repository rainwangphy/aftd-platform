import AFTD.Prelude

/-!
# perm_second_derivative

Topic: combinatorics   Node: c06c8c944f13

Provenance: formalization of a published result. Source: arXiv:2610.38237, Definition 1.1

For a permutation σ : Equiv.Perm (Fin n) and a natural number ℓ : ℕ, the discrete second derivative perm_second_derivative σ ℓ : ℤ is (σ ⟨ℓ, h1⟩ : ℤ) + (σ ⟨ℓ - 2, h0⟩ : ℤ) - 2 * (σ ⟨ℓ - 1, hm⟩ : ℤ) if 2 ≤ ℓ ∧ ℓ ≤ n - 1 (where the indices ℓ, ℓ - 2, ℓ - 1 are in Fin n), and 0 otherwise.
-/

/-- The discrete second derivative of a permutation σ at 1-based index ℓ. -/
def perm_second_derivative {n : ℕ} (σ : Equiv.Perm (Fin n)) (ℓ : ℕ) : ℤ := if h : 2 ≤ ℓ ∧ ℓ ≤ n - 1 then
    have h1 : ℓ < n := by omega
    have h0 : ℓ - 2 < n := by omega
    have hm : ℓ - 1 < n := by omega
    (σ ⟨ℓ, h1⟩ : ℤ) + (σ ⟨ℓ - 2, h0⟩ : ℤ) - 2 * (σ ⟨ℓ - 1, hm⟩ : ℤ)
  else 0
