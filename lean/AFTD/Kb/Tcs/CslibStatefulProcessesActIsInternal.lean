import AFTD.Prelude
import AFTD.Kb.Tcs.CslibStatefulProcessesAct
import AFTD.Kb.Tcs.CslibMechExpr
import AFTD.Kb.Tcs.CslibMechInstCoeExpr
import AFTD.Kb.Tcs.CslibMechInstCoeExpr1

/-!
# Cslib.StatefulProcesses.Act.isInternal

Topic: distributed   Node: f40991cfb62e

Provenance: formalization of a published result. Source: CSLib, `Cslib.StatefulProcesses.Act.isInternal`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/StatefulProcesses/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

An action is internal if it is not meant to interact with another process.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.style.header false in
set_option linter.style.longLine false in

@[expose] public section in
open Cslib.Mech in
/-- An action is internal if it is not meant to interact with another process. -/
def Cslib.StatefulProcesses.Act.isInternal : Act Pid Var Val FunId SelLabel → Bool
  | assign _ _ | condThen _ | condElse _ => true
  | _ => false
