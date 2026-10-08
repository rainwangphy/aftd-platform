import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.totalize

Topic: computability   Node: ad3c2335835c

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.totalize`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Total.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`totalize` constructs a total LTS from any given LTS by adding a sink state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib in
variable {State Label : Type*} {lts : LTS State Label} in
/-- `totalize` constructs a total LTS from any given LTS by adding a sink state. -/
def Cslib.LTS.totalize (lts : LTS State Label) : LTS (Option State) Label where
  Tr s' μ t' := match s', t' with
    | some s, some t => lts.Tr s μ t
    | _, none => True
    | none, some _ => False
