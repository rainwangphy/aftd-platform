import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCCSAct
import AFTD.Kb.Tcs.CslibCCSActIsVisible

/-!
# Cslib.CCS.Act.isVisible_neq_τ

Topic: distributed   Node: 9bf641cfdc11

Provenance: formalization of a published result. Source: CSLib, `Cslib.CCS.Act.isVisible_neq_τ`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CCS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If an action is visible, it is not `τ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
/-- If an action is visible, it is not `τ`. -/
@[scoped grind →, simp]
theorem Cslib.CCS.Act.isVisible_neq_τ {μ : Act Name} (h : μ.IsVisible) : μ ≠ Act.τ := by
  cases μ <;> grind
