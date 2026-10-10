import AFTD.Prelude
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmMk2
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun

/-!
# TriLinearSymm.mk₃

Topic: classical_mechanics   Node: f4bd3242e1b8

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm.mk₃`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The construction of a symmetric trilinear map from `smul` and `map_add` in the first factor, and two swap.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TriLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
/-- The construction of a symmetric trilinear map from `smul` and `map_add` in the first factor, and two swap. -/
@[simps!]
def TriLinearSymm.mk₃ (f : V × V × V→ ℚ) (map_smul : ∀ a S T L, f (a • S, T, L) = a * f (S, T, L))
    (map_add : ∀ S1 S2 T L, f (S1 + S2, T, L) = f (S1, T, L) + f (S2, T, L))
    (swap₁ : ∀ S T L, f (S, T, L) = f (T, S, L))
    (swap₂ : ∀ S T L, f (S, T, L) = f (S, L, T)) : TriLinearSymm V where
  toFun := fun S => (BiLinearSymm.mk₂ (fun T => f (S, T))
    (by
      intro a T L
      rw [swap₁, map_smul, swap₁])
    (by
      intro S1 S2 T
      rw [swap₁, map_add, swap₁, swap₁ S2 S T])
    (by exact fun L T ↦ swap₂ S L T)).toLinearMap
  map_add' S1 S2 := LinearMap.ext fun T ↦ LinearMap.ext fun L => map_add S1 S2 T L
  map_smul' a S :=
    LinearMap.ext fun T => LinearMap.ext fun L => map_smul a S T L
  swap₁' := swap₁
  swap₂' := swap₂
