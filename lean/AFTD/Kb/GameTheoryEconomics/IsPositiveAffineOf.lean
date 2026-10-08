import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# IsPositiveAffineOf

Topic: general_equilibrium   Node: 67ec94e1f1b4

Provenance: formalization of a published result. Source: EconCSLib, `IsPositiveAffineOf`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/AffineTransform.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`v` is a positive affine transformation of `u`: `v(x) = a · u(x) + b` with `a > 0`. Two utility functions related by a positive affine transform represent the same preference. [MSZ 2.22]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {X 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- `v` is a positive affine transformation of `u`: `v(x) = a · u(x) + b` with `a > 0`. Two utility functions related by a positive affine transform represent the same preference. [MSZ 2.22] -/
def IsPositiveAffineOf (u v : X → 𝕜) : Prop :=
  ∃ (a b : 𝕜), 0 < a ∧ ∀ x, v x = a * u x + b
