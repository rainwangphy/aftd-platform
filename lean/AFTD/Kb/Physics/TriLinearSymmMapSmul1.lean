import AFTD.Prelude
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun

/-!
# TriLinearSymm.map_smul₁

Topic: classical_mechanics   Node: 42b7ac122ab5

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm.map_smul₁`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TriLinearSymm.map_smul₁
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TriLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma TriLinearSymm.map_smul₁ (f : TriLinearSymm V) (a : ℚ) (S T L : V) :
    f (a • S) T L = a * f S T L := by
  have h : f (a • S) = a • (f S) := by
    exact f.map_smul a S
  simp [h]
