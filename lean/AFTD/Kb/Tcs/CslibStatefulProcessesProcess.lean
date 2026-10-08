import AFTD.Prelude
import AFTD.Kb.Tcs.CslibStatefulProcessesPrefix
import AFTD.Kb.Tcs.CslibMechExpr
import AFTD.Kb.Tcs.CslibMechInstCoeExpr
import AFTD.Kb.Tcs.CslibMechInstCoeExpr1

/-!
# Cslib.StatefulProcesses.Process

Topic: distributed   Node: f8b90ae85b9e

Provenance: formalization of a published result. Source: CSLib, `Cslib.StatefulProcesses.Process`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/StatefulProcesses/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Processes.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.style.header false in
set_option linter.style.longLine false in

@[expose] public section in
open Cslib.Mech in
/-- Processes. -/
inductive Cslib.StatefulProcesses.Process (Pid Var Val FunId SelLabel ProcName : Type*) where
  /-- The terminated process. -/
  | nil
  /-- Execute the prefix `prf` and proceed as the continuation `pr`. -/
  | pre (prf : Prefix Pid Var Val FunId SelLabel) (pr : Process Pid Var Val FunId SelLabel ProcName)
  /-- Branching process: receives a selection label and continues accordingly. -/
  | recvLabel (p : Pid) (branches : List (SelLabel × Process Pid Var Val FunId SelLabel ProcName))
  /-- Conditional: evaluate `e` to choose between `pr₁` and `pr₂`. -/
  | cond (e : Expr Var Val FunId) (pr₁ pr₂ : Process Pid Var Val FunId SelLabel ProcName)
  /-- Call the procedure `proc`. -/
  | call (proc : ProcName) (ps : List Pid)
