import AFTD.Prelude

/-!
# Cslib.FLP.InpEqOn

Topic: distributed   Node: 8f8bbefc980a

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLP.InpEqOn`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Distributed/FLP/CanReachVia.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`InpEqOn ps inp1 inp2` means that inputs `inp1` and `inp2` agree on all processes in `ps`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set Sum Multiset in
variable {P M S : Type*} [DecidableEq P] [DecidableEq M] in
/-- `InpEqOn ps inp1 inp2` means that inputs `inp1` and `inp2` agree on all processes in `ps`. -/
def Cslib.FLP.InpEqOn (ps : Set P) (inp1 inp2 : P → Bool) : Prop :=
  ∀ p, p ∈ ps → inp1 p = inp2 p
