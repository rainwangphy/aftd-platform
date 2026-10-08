import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFLPMessage

/-!
# Cslib.FLP.Action

Topic: distributed   Node: ec3159e48d7e

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLP.Action`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Distributed/FLP/Algorithm.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type of labels of the LTS defined by an `Algorithm`, where `some m` denotes the reception of message `m` and `none` denotes a stuttering step.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Sum Multiset in
variable {P M S : Type*} [DecidableEq P] [DecidableEq M] in
/-- The type of labels of the LTS defined by an `Algorithm`, where `some m` denotes the reception of message `m` and `none` denotes a stuttering step. -/
abbrev Cslib.FLP.Action (P M : Type*) := Option (Message P M)
