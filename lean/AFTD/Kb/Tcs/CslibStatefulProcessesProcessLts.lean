import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibStatefulProcessesProcess
import AFTD.Kb.Tcs.CslibStatefulProcessesAct
import AFTD.Kb.Tcs.CslibStatefulProcessesProcessTr
import AFTD.Kb.Tcs.CslibStatefulProcessesInstZeroProcess

/-!
# Cslib.StatefulProcesses.Process.lts

Topic: distributed   Node: f9a03758192a

Provenance: formalization of a published result. Source: CSLib, `Cslib.StatefulProcesses.Process.lts`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/StatefulProcesses/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Symbolic LTS of processes.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.style.header false in
set_option linter.style.longLine false in

@[expose] public section in
open Cslib.Mech in
/-- Symbolic LTS of processes. -/
def Cslib.StatefulProcesses.Process.lts :
    LTS (Process Pid Var Val FunId SelLabel ProcName) (Act Pid Var Val FunId SelLabel) :=
  ⟨Process.Tr⟩
