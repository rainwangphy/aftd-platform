import AFTD.Prelude
import AFTD.Kb.Tcs.CslibStatefulProcessesProcess

/-!
# Cslib.StatefulProcesses.instZeroProcess

Topic: distributed   Node: b59356f06ccf

Provenance: formalization of a published result. Source: CSLib, `Cslib.StatefulProcesses.instZeroProcess`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/StatefulProcesses/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Cslib.StatefulProcesses.instZeroProcess
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.style.header false in
set_option linter.style.longLine false in

@[expose] public section in
open Cslib.Mech in
instance Cslib.StatefulProcesses.instZeroProcess : Zero (Process Pid Var Val FunId SelLabel ProcName) := ⟨.nil⟩
