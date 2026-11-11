import AFTD.Prelude
import AFTD.Kb.Physics.F2RealCharacterValues

/-!
# f2_character_to_dual

Topic: quantum_mechanics   Node: 3c81cb47458e

Provenance: helper lemma. Binary character infrastructure for the OP-827 supported-kernel entropy reduction.

Map a real-valued character of a binary vector space to its linear functional.
-/

noncomputable def f2_character_to_dual {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (χ : AddChar M ℝ) : M →ₗ[ZMod 2] ZMod 2 :=
  ({ toFun := fun x => if χ x = 1 then 0 else 1
     map_zero' := by simp
     map_add' := by
       intro x y
       rcases f2_real_character_values χ x with hx | hx <;>
       rcases f2_real_character_values χ y with hy | hy <;>
       norm_num [AddChar.map_add_eq_mul, hx, hy]
       all_goals decide } : M →+ ZMod 2).toZModLinearMap 2
