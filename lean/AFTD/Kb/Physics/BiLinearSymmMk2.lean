import AFTD.Prelude
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun

/-!
# BiLinearSymm.mk₂

Topic: classical_mechanics   Node: 10c8a7ac9934

Provenance: formalization of a published result. Source: Physlib, `BiLinearSymm.mk₂`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The construction of a symmetric bilinear map from `smul` and `map_add` in the first factor, and swap.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BiLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
/-- The construction of a symmetric bilinear map from `smul` and `map_add` in the first factor, and swap. -/
@[simps!]
def BiLinearSymm.mk₂ (f : V × V → ℚ) (map_smul : ∀ a S T, f (a • S, T) = a * f (S, T))
    (map_add : ∀ S1 S2 T, f (S1 + S2, T) = f (S1, T) + f (S2, T))
    (swap : ∀ S T, f (S, T) = f (T, S)) : BiLinearSymm V where
  toFun := fun S => {
    toFun := fun T => f (S, T)
    map_add' := by
      intro T1 T2
      rw [swap, map_add]
      simp [swap]
    map_smul' := by
      intro a T
      simp only [RingHom.id_apply, smul_eq_mul]
      rw [swap, map_smul]
      exact congrArg (HMul.hMul a) (swap T S)
  }
  map_smul' := fun a S => LinearMap.ext fun T => map_smul a S T
  map_add' := fun S1 S2 => LinearMap.ext fun T => map_add S1 S2 T
  swap' := swap
