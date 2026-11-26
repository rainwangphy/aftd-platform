import AFTD.Prelude

/-!
# qutrit_zero_bell_partial_product_vectors

Topic: quantum   Node: 6623ecb2d9b3

Provenance: helper lemma. OP-2299 zero-Bell face support; numerical span checks in experiment 40926.

Vectors obtained by partial transposition of pure product generators on the zero-Bell face: x is orthogonal to y, and r of the k copies of y are conjugated, as is x when requested.
-/

def qutrit_zero_bell_partial_product_vectors (k r : ℕ) (transposeA : Bool) :
  Set (Fin 3 × (Fin k → Fin 3) → ℂ) := {v | ∃ x y : Fin 3 → ℂ,
    (∑ i : Fin 3, star (x i) * y i) = 0 ∧
    v = fun q => (if transposeA then star (x q.1) else x q.1) *
      ∏ j : Fin k, (if j.val < r then star (y (q.2 j)) else y (q.2 j))}
