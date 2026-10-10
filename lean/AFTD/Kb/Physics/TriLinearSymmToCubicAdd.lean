import AFTD.Prelude
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.TriLinearSymmToCubic
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmMapAdd1
import AFTD.Kb.Physics.TriLinearSymmMapAdd2
import AFTD.Kb.Physics.TriLinearSymmMapAdd3
import AFTD.Kb.Physics.TriLinearSymmSwap2
import AFTD.Kb.Physics.TriLinearSymmSwap1

/-!
# TriLinearSymm.toCubic_add

Topic: classical_mechanics   Node: 28da845d374f

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm.toCubic_add`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TriLinearSymm.toCubic_add
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TriLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
set_option backward.isDefEq.respectTransparency false in
lemma TriLinearSymm.toCubic_add {charges : Type} [AddCommMonoid charges] [Module ℚ charges]
    (τ : TriLinearSymm charges) (S T : charges) :
    τ.toCubic (S + T) = τ.toCubic S +
    τ.toCubic T + 3 * τ S S T + 3 * τ T T S := by
  simp only [HomogeneousCubic, toCubic_apply]
  rw [τ.map_add₁, τ.map_add₂, τ.map_add₂, τ.map_add₃, τ.map_add₃, τ.map_add₃, τ.map_add₃]
  rw [τ.swap₂ S T S, τ.swap₁ T S S, τ.swap₂ S T S, τ.swap₂ T S T, τ.swap₁ S T T, τ.swap₂ T S T]
  grind
