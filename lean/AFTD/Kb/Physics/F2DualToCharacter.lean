import AFTD.Prelude
import AFTD.Kb.Physics.F2ValueCases

/-!
# f2_dual_to_character

Topic: quantum_mechanics   Node: b30a39ad6df3

Provenance: helper lemma. Binary character infrastructure for the OP-827 supported-kernel entropy reduction.

Map a binary linear functional to its associated real-valued character.
-/

noncomputable def f2_dual_to_character {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (f : M →ₗ[ZMod 2] ZMod 2) : AddChar M ℝ where
  toFun x := if f x = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro x y
    rcases f2_value_cases (f x) with hx | hx <;>
    rcases f2_value_cases (f y) with hy | hy <;>
    norm_num [map_add, hx, hy]
    all_goals decide
