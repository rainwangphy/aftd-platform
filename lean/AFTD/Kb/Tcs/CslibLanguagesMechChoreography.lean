import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLanguagesMechExpr
import AFTD.Kb.Tcs.CslibLanguagesMechPrefix
import AFTD.Kb.Tcs.CslibLanguagesMechInstCoeExpr
import AFTD.Kb.Tcs.CslibLanguagesMechInstCoeExpr1

/-!
# Cslib.Languages.Mech.Choreography

Topic: distributed   Node: b7e5d451d34e

Provenance: formalization of a published result. Source: CSLib, `Cslib.Languages.Mech.Choreography`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/Choreography/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Choreographies.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Choreographies. -/
inductive Cslib.Languages.Mech.Choreography (Pid Var Val FunId SelLabel ProcName : Type*) where
  /-- The terminated choreography. -/
  | nil
  /-- Do `prf` and continue as `c`. -/
  | pre (prf : Prefix Pid Var Val FunId SelLabel)
    (c : Choreography Pid Var Val FunId SelLabel ProcName)
  /-- Conditional: `p` evaluates `e` to choose between `c₁` and `c₂`. -/
  | cond (p : Pid) (e : Expr Var Val FunId)
    (c₁ c₂ : Choreography Pid Var Val FunId SelLabel ProcName)
  /-- Call the procedure `proc`. -/
  | call (proc : ProcName) (ps : List Pid)
