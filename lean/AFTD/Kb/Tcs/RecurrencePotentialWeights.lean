import AFTD.Prelude

/-!
# recurrence_potential_weights

Topic: combinatorics   Node: f62453ae15c8

Provenance: formalization of a published result. Source: arXiv:2611.01561, Proof of Lemma 2.1

For N : ℕ, a, c : Fin (N + 1) → ℝ, and i : Fin (N + 1), the potential weight π_i is the product over j < i.val of a(j) / c(j + 1).
-/

/-- Potential weights π_i for a finite recurrence array, defined by π_0 = 1 and π_{i+1} = π_i * a_i / c_{i+1}. -/
noncomputable def recurrence_potential_weights (N : ℕ) (a c : Fin (N + 1) → ℝ)
    (i : Fin (N + 1)) : ℝ := ∏ j : Fin i.val,
    a ⟨j.val, lt_trans j.isLt i.isLt⟩ /
    c ⟨j.val + 1, Nat.lt_of_le_of_lt (Nat.succ_le_of_lt j.isLt) i.isLt⟩
