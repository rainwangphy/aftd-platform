import AFTD.Prelude

/-!
# dephased_path_local_noise_criterion

Topic: quantum_mechanics   Node: 2dad50317962

Provenance: formalization of a published result. Source: arXiv:2511.19585, Monogamy of Mutual Information in Graph States

For n : ℕ and q : Fin n → ℝ, dephased_path_local_noise_criterion n q holds if for every natural number i with 1 ≤ i and i + 1 < n, q ⟨i, by omega⟩ ≥ q ⟨i - 1, by omega⟩ * q ⟨i + 1, by omega⟩.
-/

/-- Local noise criterion q_i >= q_{i-1} * q_{i+1} for all 1 <= i <= n-2 on a path of length n. -/
def dephased_path_local_noise_criterion (n : ℕ) (q : Fin n → ℝ) : Prop := ∀ (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 < n),
  q ⟨i, by omega⟩ ≥ q ⟨i - 1, by omega⟩ * q ⟨i + 1, by omega⟩
