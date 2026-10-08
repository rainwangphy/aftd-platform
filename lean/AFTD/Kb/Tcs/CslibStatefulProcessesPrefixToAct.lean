import AFTD.Prelude
import AFTD.Kb.Tcs.CslibStatefulProcessesPrefix
import AFTD.Kb.Tcs.CslibMechExpr
import AFTD.Kb.Tcs.CslibMechInstCoeExpr
import AFTD.Kb.Tcs.CslibStatefulProcessesAct
import AFTD.Kb.Tcs.CslibMechInstCoeExpr1

/-!
# Cslib.StatefulProcesses.Prefix.toAct

Topic: distributed   Node: 8d3544b457b4

Provenance: formalization of a published result. Source: CSLib, `Cslib.StatefulProcesses.Prefix.toAct`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/StatefulProcesses/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Transforms a `Prefix` into an `Act`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.style.header false in
set_option linter.style.longLine false in

@[expose] public section in
open Cslib.Mech in
/-- Transforms a `Prefix` into an `Act`. -/
abbrev Cslib.StatefulProcesses.Prefix.toAct : Prefix Pid Var Val FunId SelLabel → Act Pid Var Val FunId SelLabel
  | assign x e => .assign x e
  | sendValue p e => .sendValue p e
  | recvValue p x => .recvValue p x
  | sendLabel p l => .sendLabel p l
