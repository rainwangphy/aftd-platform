import AFTD.Prelude

/-!
# Cslib.FLP.ProcState

Topic: distributed   Node: d75bee0a2f90

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLP.ProcState`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Distributed/FLP/Algorithm.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type of a process's local state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Sum Multiset in
variable {P M S : Type*} [DecidableEq P] [DecidableEq M] in
/-- The type of a process's local state. -/
structure Cslib.FLP.ProcState (S : Type*) where
  /-- The internal state of a process. -/
  state : S
  /-- The state component used by a process to signal the boolean value it decides on. -/
  out : Option Bool
