import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasShiftEquiv

/-!
# dual_melas_shift_equiv_refl

Topic: information   Node: 1663f202fdbc

Provenance: helper lemma. arXiv:2610.38017 Definition 3

Shift equivalence modulo the product of minimal polynomials of α and α⁻¹ is reflexive.
-/

/-- Shift equivalence is reflexive. -/
theorem dual_melas_shift_equiv_refl {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (α : F) (f : Polynomial (ZMod 2)) :
    dual_melas_shift_equiv α f f := ⟨0, by simp⟩
