import AFTD.Prelude

/-!
# Cslib.Mech.AtPid

Topic: distributed   Node: a0138cfe2a8a

Provenance: formalization of a published result. Source: CSLib, `Cslib.Mech.AtPid`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/LocalComputation.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Type of an element of type `α` located at a process.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Type of an element of type `α` located at a process. -/
abbrev Cslib.Mech.AtPid Pid α := Pid × α
