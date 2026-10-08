import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCCSAct
import AFTD.Kb.Tcs.CslibCCSActCo
import AFTD.Kb.Tcs.CslibCCSActIsVisible

/-!
# Cslib.CCS.Act.co_isVisible

Topic: distributed   Node: aa71d33f5dde

Provenance: formalization of a published result. Source: CSLib, `Cslib.CCS.Act.co_isVisible`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CCS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If two actions are one the coaction of the other, then they are both visible.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
/-- If two actions are one the coaction of the other, then they are both visible. -/
@[scoped grind →]
theorem Cslib.CCS.Act.co_isVisible (h : Act.Co μ μ') : μ.IsVisible ∧ μ'.IsVisible := by grind
