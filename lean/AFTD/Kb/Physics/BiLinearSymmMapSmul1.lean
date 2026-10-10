import AFTD.Prelude
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun

/-!
# BiLinearSymm.map_smul₁

Topic: classical_mechanics   Node: 26d4ae685f6b

Provenance: formalization of a published result. Source: Physlib, `BiLinearSymm.map_smul₁`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BiLinearSymm.map_smul₁
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BiLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma BiLinearSymm.map_smul₁ (f : BiLinearSymm V) (a : ℚ) (S T : V) : f (a • S) T = a * f S T := by
  have h : f (a • S) = a • (f S) := by
    exact f.map_smul a S
  simp [h]
