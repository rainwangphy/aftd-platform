import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMechFunCallEval
import AFTD.Kb.Tcs.CslibMechLocalStore
import AFTD.Kb.Tcs.CslibMechExpr
import AFTD.Kb.Tcs.CslibMechInstCoeExpr
import AFTD.Kb.Tcs.CslibMechInstCoeExpr1

/-!
# Cslib.Mech.FunCallEval.EvalExpr

Topic: distributed   Node: 7bdfca3bceab

Provenance: formalization of a published result. Source: CSLib, `Cslib.Mech.FunCallEval.EvalExpr`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/LocalComputation.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Evaluation relation for expressions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Evaluation relation for expressions. -/
inductive Cslib.Mech.FunCallEval.EvalExpr (eval : FunCallEval FunId Val) :
    (σ : LocalStore Var Val) → (e : Expr Var Val FunId) → (v : Val) → Prop where
  /-- A value evaluates to itself. -/
  | val : eval.EvalExpr σ (.val v) v
  /-- A variable evaluates to its mapped value in the store. -/
  | var : eval.EvalExpr σ (.var x) (σ x)
  /-- A function call first recursively evaluates its expression arguments, and then
  invokes the parameter for function evaluation. -/
  | call
    (hArgs : List.Forall₂ (eval.EvalExpr σ) args vals)
    (hFun : eval f vals v) :
    eval.EvalExpr σ (.call f args) v
