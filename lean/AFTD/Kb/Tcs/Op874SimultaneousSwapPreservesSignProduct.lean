import AFTD.Prelude

/-!
# op874_simultaneous_swap_preserves_sign_product

Topic: combinatorics   Node: 1e73d1e3e874

Provenance: helper lemma. High-color component-swap invariant for OP-874; experiments 43221–43223.

Applying the same transposition to two finite permutations preserves the product of their signs.
-/

theorem op874_simultaneous_swap_preserves_sign_product
    {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) (σ τ : Equiv.Perm α) :
    Equiv.Perm.sign (Equiv.swap a b * σ) * Equiv.Perm.sign (Equiv.swap a b * τ) =
      Equiv.Perm.sign σ * Equiv.Perm.sign τ := by
  simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
