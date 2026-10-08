import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMechExpr
import AFTD.Kb.Tcs.CslibStatefulProcessesProcess
import AFTD.Kb.Tcs.CslibStatefulProcessesAct
import AFTD.Kb.Tcs.CslibStatefulProcessesPrefix
import AFTD.Kb.Tcs.CslibStatefulProcessesPrefixToAct
import AFTD.Kb.Tcs.CslibMechInstCoeExpr
import AFTD.Kb.Tcs.CslibMechInstCoeExpr1
import AFTD.Kb.Tcs.CslibStatefulProcessesInstZeroProcess

/-!
# Cslib.StatefulProcesses.Process.Tr

Topic: distributed   Node: 6a5e991a3229

Provenance: formalization of a published result. Source: CSLib, `Cslib.StatefulProcesses.Process.Tr`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/StatefulProcesses/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Symbolic transition relation for processes. Do not use this directly, use `Process.lts` instead.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.style.header false in
set_option linter.style.longLine false in

@[expose] public section in
open Cslib.Mech in
/-- Symbolic transition relation for processes. Do not use this directly, use `Process.lts` instead. -/
inductive Cslib.StatefulProcesses.Process.Tr :
    Process Pid Var Val FunId SelLabel ProcName → Act Pid Var Val FunId SelLabel →
    Process Pid Var Val FunId SelLabel ProcName → Prop | pre : Tr (pre prf pr) prf.toAct (pr)
  | condThen : Tr (cond e pr₁ pr₂) (.condThen e) pr₁
  | condElse : Tr (cond e pr₁ pr₂) (.condElse e) pr₂
  | recvLabel (h : (l, pr) ∈ branches): Tr (recvLabel p branches) (.recvLabel p l) pr
