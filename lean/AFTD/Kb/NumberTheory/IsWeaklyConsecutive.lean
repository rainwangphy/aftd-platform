import AFTD.Prelude

/-!
# is_weakly_consecutive

Topic: elementary_number_theory   Node: 07f3aab72c50

A permutation s of {1, ..., k} is weakly consecutive if for all positions i, j and every m, whenever m divides s(i) and m divides i - j, m also divides s(j). Here the permutation is a σ on {0, ..., k-1} with s(i+1) = σ(i) + 1.
-/

/-- A weakly consecutive sequence (Garrison-Seiler-Knowles, arXiv:2401.09497, Def. 1.1): if `m ∣ σ(i)` and `m ∣ i - j` then `m ∣ σ(j)`. Positions and values are shifted down by one: `σ : Equiv.Perm (Fin k)` stands for the permutation `i + 1 ↦ σ i + 1` of `{1, …, k}`. -/
def is_weakly_consecutive {k : ℕ} (σ : Equiv.Perm (Fin k)) : Prop :=
  ∀ (m : ℕ) (i j : Fin k), m ∣ (σ i : ℕ) + 1 → (m : ℤ) ∣ (i : ℤ) - (j : ℤ) → m ∣ (σ j : ℕ) + 1
