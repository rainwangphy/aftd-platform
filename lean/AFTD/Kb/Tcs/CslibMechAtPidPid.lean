import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMechAtPid

/-!
# Cslib.Mech.AtPid.pid

Topic: distributed   Node: dc24924e1d86

Provenance: formalization of a published result. Source: CSLib, `Cslib.Mech.AtPid.pid`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/LocalComputation.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The process name of a located element.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The process name of a located element. -/
abbrev Cslib.Mech.AtPid.pid (a : AtPid Pid α) := a.fst
