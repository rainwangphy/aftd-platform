import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLanguagesMechExpr

/-!
# Cslib.Languages.Mech.instCoeExpr

Topic: distributed   Node: b9ef89a6d4a8

Provenance: formalization of a published result. Source: CSLib, `Cslib.Languages.Mech.instCoeExpr`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/Choreography/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Utility instance to write variables directly as expressions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Utility instance to write variables directly as expressions. -/
instance Cslib.Languages.Mech.instCoeExpr : Coe Var (Expr Var Val FunId) where
  coe x := .var x
