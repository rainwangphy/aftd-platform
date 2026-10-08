import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMechAtPid

/-!
# Cslib.Mech.AtPid.elem

Topic: distributed   Node: fee0fb56021a

Provenance: formalization of a published result. Source: CSLib, `Cslib.Mech.AtPid.elem`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/LocalComputation.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The element of a located element.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The element of a located element. -/
abbrev Cslib.Mech.AtPid.elem (a : AtPid Pid α) := a.snd
