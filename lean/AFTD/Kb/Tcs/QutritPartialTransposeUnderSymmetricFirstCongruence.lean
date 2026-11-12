import AFTD.Prelude

/-!
# qutrit_partial_transpose_under_symmetric_first_congruence

Topic: quantum   Node: 3d84f98eff49

Provenance: helper lemma. Local compatibility helper for OP-693.

Partial-transpose invariance survives a transpose congruence on the first factor.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem qutrit_partial_transpose_under_symmetric_first_congruence
    {m : ℕ} (ρ : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℂ)
    (H : Matrix (Fin 3) (Fin 3) ℂ)
    (hpt : ∀ i j : Fin 3, ∀ p q : Fin m, ρ (i,p) (j,q) = ρ (j,p) (i,q)) :
    ∀ a c : Fin 3, ∀ p q : Fin m,
      (∑ i : Fin 3, ∑ j : Fin 3, H a i * ρ (i,p) (j,q) * H c j) =
      ∑ i : Fin 3, ∑ j : Fin 3, H c i * ρ (i,p) (j,q) * H a j := by
  intro a c p q
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hpt i j p q]
  ring
