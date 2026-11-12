import AFTD.Prelude

/-!
# qutrit_partial_transpose_hermitian_block_structure

Topic: quantum   Node: 15f8e0ab15df

Provenance: helper lemma. Local compatibility helper for OP-693.

For a partial-transpose-invariant Hermitian 3-by-2 matrix, the off-diagonal qutrit block is symmetric and both diagonal qutrit blocks are entrywise real.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem qutrit_partial_transpose_hermitian_block_structure
    (X : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) (hX : X.IsHermitian)
    (hpt : ∀ i j : Fin 3, ∀ p q : Fin 2, X (i,p) (j,q) = X (j,p) (i,q)) :
    (let B : Matrix (Fin 3) (Fin 3) ℂ := fun i j => X (i,0) (j,1); B.transpose = B) ∧
    (∀ i j : Fin 3, ∀ p : Fin 2, star (X (i,p) (j,p)) = X (i,p) (j,p)) := by
  constructor
  · ext i j
    exact hpt j i 0 1
  · intro i j p
    calc
      star (X (i,p) (j,p)) = X (j,p) (i,p) := hX.apply (j,p) (i,p)
      _ = X (i,p) (j,p) := hpt j i p p
