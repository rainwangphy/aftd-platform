import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMechLocalStore

/-!
# Cslib.Mech.GlobalStore

Topic: distributed   Node: ab64ece80090

Provenance: formalization of a published result. Source: CSLib, `Cslib.Mech.GlobalStore`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/LocalComputation.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A global store represents the memory state of an entire system, mapping each process to its local store.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A global store represents the memory state of an entire system, mapping each process to its local store. -/
abbrev Cslib.Mech.GlobalStore Pid Var Val := (p : Pid) → LocalStore Var Val
