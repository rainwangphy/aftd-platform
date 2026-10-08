import AFTD.Prelude

/-!
# Cslib.Mech.LocalStore

Topic: distributed   Node: ff7f0c2171eb

Provenance: formalization of a published result. Source: CSLib, `Cslib.Mech.LocalStore`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/LocalComputation.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A local store represents the memory state of a process, mapping variables to values.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A local store represents the memory state of a process, mapping variables to values. -/
abbrev Cslib.Mech.LocalStore Var Val := (x : Var) → Val
