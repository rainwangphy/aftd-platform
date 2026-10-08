import AFTD.Prelude
import AFTD.Kb.Tcs.CslibStatefulProcessesNetwork
import AFTD.Kb.Tcs.CslibStatefulProcessesProcess
import AFTD.Kb.Tcs.CslibStatefulProcessesInstZeroProcess

/-!
# Cslib.StatefulProcesses.instZeroNetwork

Topic: distributed   Node: 4ef50c7b68f6

Provenance: formalization of a published result. Source: CSLib, `Cslib.StatefulProcesses.instZeroNetwork`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/StatefulProcesses/Network.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The 0 ('zero') network, mapping all processes to the process term 0.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib.Mech in
/-- The 0 ('zero') network, mapping all processes to the process term 0. -/
instance Cslib.StatefulProcesses.instZeroNetwork : Zero (Network Pid Var Val FunId SelLabel ProcName) := ⟨fun _ => 0⟩
