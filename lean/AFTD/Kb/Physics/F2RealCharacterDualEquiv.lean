import AFTD.Prelude
import AFTD.Kb.Physics.F2CharacterToDual
import AFTD.Kb.Physics.F2DualToCharacter
import AFTD.Kb.Physics.F2RealCharacterValues
import AFTD.Kb.Physics.F2ValueCases

/-!
# f2_real_character_dual_equiv

Topic: quantum_mechanics   Node: 57720a816bfa

Provenance: helper lemma. Binary character infrastructure for the OP-827 supported-kernel entropy reduction.

Real-valued additive characters of a binary vector space are equivalent to its linear dual.
-/

noncomputable def f2_real_character_dual_equiv {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] :
    AddChar M ℝ ≃ (M →ₗ[ZMod 2] ZMod 2) where
  toFun := f2_character_to_dual
  invFun := f2_dual_to_character
  left_inv := by
    intro χ
    ext x
    rcases f2_real_character_values χ x with hx | hx <;>
    norm_num [f2_character_to_dual, f2_dual_to_character, hx]
  right_inv := by
    intro f
    ext x
    rcases f2_value_cases (f x) with hx | hx <;>
    norm_num [f2_character_to_dual, f2_dual_to_character, hx]
