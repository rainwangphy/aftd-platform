import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMechExpr
import AFTD.Kb.Tcs.CslibMechInstCoeExpr
import AFTD.Kb.Tcs.CslibMechInstCoeExpr1

/-!
# Cslib.StatefulProcesses.Act

Topic: distributed   Node: 5ab8fecd5b98

Provenance: formalization of a published result. Source: CSLib, `Cslib.StatefulProcesses.Act`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/StatefulProcesses/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Actions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.style.header false in
set_option linter.style.longLine false in

@[expose] public section in
open Cslib.Mech in
/-- Actions. -/
inductive Cslib.StatefulProcesses.Act (Pid Var Val FunId SelLabel : Type*) where
  /-- Assign to `x` the result of evaluating `e`. -/
  | assign (x : Var) (e : Expr Var Val FunId)
  /-- Send to `p` the result of evaluating `e`. -/
  | sendValue (p : Pid) (e : Expr Var Val FunId)
  /-- Receive a value from `p` and store it in variable `x`. -/
  | recvValue (p : Pid) (x : Var)
  /-- Send to `p` the selection label `l`. -/
  | sendLabel (p : Pid) (l : SelLabel)
  /-- Receive from `p` the selection label `l`. -/
  | recvLabel (p : Pid) (l : SelLabel)
  /-- Choose the then-branch of a conditional guarded by `e`. -/
  | condThen (e : Expr Var Val FunId)
  /-- Choose the else-branch of a conditional guarded by `e`. -/
  | condElse (e : Expr Var Val FunId)
