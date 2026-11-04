import AFTD.Prelude

/-!
# newton_coeff

Topic: combinatorics   Node: d9d8b3d4e35a

Provenance: formalization of a published result. Source: arXiv:2611.01561 Sec. 3

For N : ℕ, d : Fin (N + 1) → ℝ, and k : ℕ, the k-th Newton coefficient is the sum over i from 0 to k of (-1)^(k - i) * (k choose i) * d(i) when i < N + 1, and 0 otherwise.
-/

/-- Newton coefficients of a sequence d on Fin (N + 1). -/
noncomputable def newton_coeff (N : ℕ) (d : Fin (N + 1) → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1),
    if h : i < N + 1 then
      (-1 : ℝ) ^ (k - i) * (Nat.choose k i : ℝ) * d ⟨i, h⟩
    else 0
