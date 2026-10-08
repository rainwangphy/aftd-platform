import AFTD.Prelude
import AFTD.Kb.Tcs.CslibStatefulProcessesAct
import AFTD.Kb.Tcs.CslibMechExpr
import AFTD.Kb.Tcs.CslibMechInstCoeExpr
import AFTD.Kb.Tcs.CslibMechInstCoeExpr1

/-!
# Cslib.StatefulProcesses.Network.TrLabel

Topic: distributed   Node: fe38c064efb2

Provenance: formalization of a published result. Source: CSLib, `Cslib.StatefulProcesses.Network.TrLabel`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/StatefulProcesses/Network.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Symbolic transition labels for networks.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib.Mech in
/-- Symbolic transition labels for networks. -/
inductive Cslib.StatefulProcesses.Network.TrLabel Pid Var Val FunId SelLabel | local (p : Pid) (μ : Act Pid Var Val FunId SelLabel)
  | com (p : Pid) (e : Expr Var Val FunId) (q : Pid) (x : Var)
  | sel (p : Pid) (q : Pid) (l : SelLabel)
