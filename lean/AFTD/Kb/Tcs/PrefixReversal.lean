import AFTD.Prelude

/-!
# prefixReversal

Topic: combinatorics   Node: 30166eb65d34

Provenance: formalization of a published result. Source: arXiv:2610.30892 Section 1

For integers n and k, prefixReversal n k is the permutation in the symmetric group Equiv.Perm (Fin n) that reverses the first k elements (indices 0 through k - 1) and fixes all remaining elements.
-/

/-- The prefix reversal permutation in Equiv.Perm (Fin n) reversing the first k elements. -/
def prefixReversal (n : ℕ) (k : ℕ) : Equiv.Perm (Fin n) := {
  toFun := fun j =>
    if h : j.val < k ∧ k ≤ n then
      ⟨k - 1 - j.val, by omega⟩
    else j
  invFun := fun j =>
    if h : j.val < k ∧ k ≤ n then
      ⟨k - 1 - j.val, by omega⟩
    else j
  left_inv := by
    intro ⟨j, hj⟩
    dsimp
    by_cases h : j < k ∧ k ≤ n
    · rw [dif_pos h]
      have h' : k - 1 - j < k ∧ k ≤ n := by omega
      rw [dif_pos h']
      apply Fin.ext; dsimp; omega
    · rw [dif_neg h, dif_neg h]
  right_inv := by
    intro ⟨j, hj⟩
    dsimp
    by_cases h : j < k ∧ k ≤ n
    · rw [dif_pos h]
      have h' : k - 1 - j < k ∧ k ≤ n := by omega
      rw [dif_pos h']
      apply Fin.ext; dsimp; omega
    · rw [dif_neg h, dif_neg h]
}
