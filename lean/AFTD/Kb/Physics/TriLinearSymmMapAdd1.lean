import AFTD.Prelude
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun

/-!
# TriLinearSymm.map_add₁

Topic: classical_mechanics   Node: f3ae0073c17f

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm.map_add₁`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TriLinearSymm.map_add₁
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TriLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
lemma TriLinearSymm.map_add₁ (f : TriLinearSymm V) (S1 S2 T L : V) :
    f (S1 + S2) T L = f S1 T L + f S2 T L := by
  have h : f (S1 + S2) = f S1 + f S2 := by
    exact f.map_add S1 S2
  simp [h]
