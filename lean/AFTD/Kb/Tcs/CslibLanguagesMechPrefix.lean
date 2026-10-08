import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLanguagesMechExpr
import AFTD.Kb.Tcs.CslibLanguagesMechInstCoeExpr
import AFTD.Kb.Tcs.CslibLanguagesMechInstCoeExpr1

/-!
# Cslib.Languages.Mech.Prefix

Topic: distributed   Node: e4a407a01e77

Provenance: formalization of a published result. Source: CSLib, `Cslib.Languages.Mech.Prefix`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/Choreography/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Choreographic prefix.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Choreographic prefix. -/
inductive Cslib.Languages.Mech.Prefix (Pid Var Val FunId SelLabel : Type*) where
  /-- `p` assigns `x` the value computed from `e`. -/
  | assign (p : Pid) (x : Var) (e : Expr Var Val FunId)
  /-- `p` communicates the evaluation of `e` to `q`, which stores it in its variable `x`. -/
  | com (p : Pid) (e : Expr Var Val FunId) (q : Pid) (x : Var)
  /-- `p` communicates the selection label (a static tag used to denote a choice) to `q`. -/
  | sel (p : Pid) (q : Pid) (l : SelLabel)
