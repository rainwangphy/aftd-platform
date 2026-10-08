import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFLPMessage
import AFTD.Kb.Tcs.CslibFLPProcState

/-!
# Cslib.FLP.Algorithm

Topic: distributed   Node: 64d0ecc834d0

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLP.Algorithm`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Distributed/FLP/Algorithm.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The specification of a distributed algorithm for solving the consensus problem. Note that each field below can depend on a process's identifier (recall that each `Message` contains its destination's identifier), so the algorithm is not required to be uniform across processes.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Sum Multiset in
variable {P M S : Type*} [DecidableEq P] [DecidableEq M] in
/-- The specification of a distributed algorithm for solving the consensus problem. Note that each field below can depend on a process's identifier (recall that each `Message` contains its destination's identifier), so the algorithm is not required to be uniform across processes. -/
structure Cslib.FLP.Algorithm (P M S : Type*) where
  /-- A map specifying the initial state of each process. -/
  init : P → S
  /-- A map specifying how a process changes its internal state upon receiving a message. -/
  next : Message P M → ProcState S → S
  /-- A map specifying what messages a process sends out upon receiving a message. -/
  send : Message P M → ProcState S → Multiset (Message P M)
  /-- A map specifying the boolean decision a process makes upon receiving a message,
      where `none` means that no decision is made. -/
  out : Message P M → ProcState S → Option Bool
