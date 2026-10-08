import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFLPMessage
import AFTD.Kb.Tcs.CslibFLPProcState

/-!
# Cslib.FLP.State

Topic: distributed   Node: 2c9ea5864b74

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLP.State`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Distributed/FLP/Algorithm.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The global state of the distributed algorithm.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Sum Multiset in
variable {P M S : Type*} [DecidableEq P] [DecidableEq M] in
/-- The global state of the distributed algorithm. -/
structure Cslib.FLP.State (P M S : Type*) where
  /-- A multiset containing all messages that are in-flight (namely, they have been sent but
  not yet received). Note that being a multiset implies that the messages are not ordered. -/
  msgs : Multiset (Message P M)
  /-- A map giving the local states of all processes. -/
  proc : P → ProcState S
