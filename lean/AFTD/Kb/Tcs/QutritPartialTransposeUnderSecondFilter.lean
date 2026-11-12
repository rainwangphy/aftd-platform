import AFTD.Prelude

/-!
# qutrit_partial_transpose_under_second_filter

Topic: quantum   Node: d6c533c88b62

Provenance: helper lemma. Local compatibility helper for OP-693.

Partial-transpose invariance survives any linear transformation on the second factor.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem qutrit_partial_transpose_under_second_filter
    {n m : ℕ} (ρ : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ)
    (W : Matrix (Fin n) (Fin m) ℂ)
    (hpt : ∀ a c : Fin 3, ∀ x y : Fin n, ρ (a,x) (c,y) = ρ (c,x) (a,y)) :
    ∀ a c : Fin 3, ∀ p q : Fin m,
      (∑ x : Fin n, ∑ y : Fin n, star (W x p) * ρ (a,x) (c,y) * W y q) =
      ∑ x : Fin n, ∑ y : Fin n, star (W x p) * ρ (c,x) (a,y) * W y q := by
  intro a c p q
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [hpt a c x y]
