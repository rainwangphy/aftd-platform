import AFTD.Prelude
import AFTD.Kb.Tcs.NonzeroCubes

/-!
# nonzero_cubes_mul

Topic: cryptography   Node: 4a4d8bf0074e

Provenance: helper lemma. arXiv:2611.10269 Sec. 7

In any field, the product of two nonzero cubes is itself a nonzero cube.
-/

/-- The product of two nonzero cubes in a field is a nonzero cube. -/
theorem nonzero_cubes_mul {E : Type*} [Field E] {x y : E} (hx : x ∈ nonzero_cubes E) (hy : y ∈ nonzero_cubes E) : x * y ∈ nonzero_cubes E := by
  rcases hx with ⟨a, ha, rfl⟩
  rcases hy with ⟨b, hb, rfl⟩
  exact ⟨a * b, mul_ne_zero ha hb, by ring⟩
