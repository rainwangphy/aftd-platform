import AFTD.Prelude
import AFTD.Kb.Tcs.CslibStatefulProcessesProcess
import AFTD.Kb.Tcs.CslibStatefulProcessesInstZeroProcess

/-!
# Cslib.StatefulProcesses.Network

Topic: distributed   Node: cee97f96a3fd

Provenance: formalization of a published result. Source: CSLib, `Cslib.StatefulProcesses.Network`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/StatefulProcesses/Network.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A network maps process names to process terms.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib.Mech in
/-- A network maps process names to process terms. -/
abbrev Cslib.StatefulProcesses.Network (Pid Var Val FunId SelLabel ProcName : Type*) :=
  Pid → Process Pid Var Val FunId SelLabel ProcName
