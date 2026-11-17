import AFTD.Prelude

/-!
# xx_interaction_hamiltonian

Topic: quantum_mechanics   Node: 2095cd8ebd8b

Provenance: formalization of a published result. Source: arXiv:2611.05010, Sec. VI

The interaction Hamiltonian V of an open XX spin chain of length n is the sum of nearest-neighbor flip-flop exchange terms, acting on computational basis states by hopping excitations between adjacent sites.
-/

open scoped Classical in
/-- Open XX chain nearest-neighbor exchange interaction V = (1/2) sum_{i=1}^{n-1} (X_i X_{i+1} + Y_i Y_{i+1}). -/
noncomputable def xx_interaction_hamiltonian (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ := fun s s' =>
  if ∃ (i : ℕ) (hi : i + 1 < n),
    s ⟨i, Nat.lt_of_succ_lt hi⟩ ≠ s ⟨i + 1, hi⟩ ∧
    s' ⟨i, Nat.lt_of_succ_lt hi⟩ = s ⟨i + 1, hi⟩ ∧
    s' ⟨i + 1, hi⟩ = s ⟨i, Nat.lt_of_succ_lt hi⟩ ∧
    (∀ (j : ℕ) (hj : j < n), j ≠ i → j ≠ i + 1 → s' ⟨j, hj⟩ = s ⟨j, hj⟩)
  then (1 : ℂ) else 0
