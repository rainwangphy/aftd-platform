import AFTD.Prelude
import AFTD.Kb.Physics.UnitaryOneParameterGroup
import AFTD.Kb.Physics.UnitaryOneParameterGroupInstCoeFunForallRealContinuousLinearMapComplexId

/-!
# UnitaryOneParameterGroup.ext

Topic: classical_mechanics   Node: 72d08f4ada03

Provenance: formalization of a published result. Source: Physlib, `UnitaryOneParameterGroup.ext`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/OneParameterSubgroups/Unitary.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

UnitaryOneParameterGroup.ext
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open UnitaryOneParameterGroup in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
@[ext]
lemma UnitaryOneParameterGroup.ext {U V : UnitaryOneParameterGroup H} (h : ∀ t, U t = V t) : U = V := by
  cases U
  cases V
  congr
  exact AddChar.ext _ _ h
