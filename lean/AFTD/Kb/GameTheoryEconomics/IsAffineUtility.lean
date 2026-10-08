import AFTD.Prelude

/-!
# IsAffineUtility

Topic: general_equilibrium   Node: c44ed44e197f

Provenance: formalization of a published result. Source: EconCSLib, `IsAffineUtility`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A utility function is affine (linear + constant): `u(x) = a·x + b`. An agent with an affine utility function is risk neutral. [MSZ 2.24]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
set_option linter.unusedSectionVars false in
/-- A utility function is affine (linear + constant): `u(x) = a·x + b`. An agent with an affine utility function is risk neutral. [MSZ 2.24] -/
def IsAffineUtility (u : 𝕜 → 𝕜) : Prop :=
  ∃ (a b : 𝕜), ∀ x, u x = a * x + b
