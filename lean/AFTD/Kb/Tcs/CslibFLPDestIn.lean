import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFLPAction
import AFTD.Kb.Tcs.CslibFLPMessage

/-!
# Cslib.FLP.DestIn

Topic: distributed   Node: 6001ae09058b

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLP.DestIn`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Distributed/FLP/Algorithm.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`DestIn ps x` means that if `x ≠ none`, then `x = some m` with `m.dest ∈ ps`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Sum Multiset in
variable {P M S : Type*} [DecidableEq P] [DecidableEq M] in
/-- `DestIn ps x` means that if `x ≠ none`, then `x = some m` with `m.dest ∈ ps`. -/
def Cslib.FLP.DestIn (ps : Set P) : Action P M → Prop
  | some m => m.dest ∈ ps
  | none => True
