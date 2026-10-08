import AFTD.Prelude

/-!
# Cslib.FLP.Message

Topic: distributed   Node: 94919189c7ef

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLP.Message`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Distributed/FLP/Algorithm.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type of messages that processes send to each other.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Sum Multiset in
variable {P M S : Type*} [DecidableEq P] [DecidableEq M] in
/-- The type of messages that processes send to each other. -/
@[ext]
structure Cslib.FLP.Message (P M : Type*) where
  /-- The destination of a message. -/
  dest : P
  /-- The content of the message, where the `Bool` option is used to carry to the
      initial boolean value to each process. -/
  msg : Bool ⊕ M
deriving DecidableEq
