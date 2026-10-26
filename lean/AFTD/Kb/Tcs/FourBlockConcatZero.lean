import AFTD.Prelude
import AFTD.Kb.Tcs.FourBlockConcat

/-!
# four_block_concat_zero

Topic: information   Node: 27d5b963ba3f

Provenance: helper lemma. arXiv:2610.29807, Section 2.3

For any natural number m, the four-block concatenation four_block_concat 0 0 0 0 of four zero Boolean functions on Fin m → ZMod 2 equals the zero Boolean function on Fin (m + 2) → ZMod 2.
-/

/-- The four-block concatenation of four zero functions is the zero function. -/
theorem four_block_concat_zero {m : ℕ} :
    four_block_concat (0 : (Fin m → ZMod 2) → ZMod 2) 0 0 0 = 0 := by
  ext v
  simp [four_block_concat]
