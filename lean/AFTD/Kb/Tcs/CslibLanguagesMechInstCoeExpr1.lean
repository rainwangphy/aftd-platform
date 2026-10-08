import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLanguagesMechExpr
import AFTD.Kb.Tcs.CslibLanguagesMechInstCoeExpr

/-!
# Cslib.Languages.Mech.instCoeExpr_1

Topic: distributed   Node: dbb7e0fbd3a2

Provenance: formalization of a published result. Source: CSLib, `Cslib.Languages.Mech.instCoeExpr_1`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/Choreography/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Utility instance to write values directly as expressions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Utility instance to write values directly as expressions. -/
instance Cslib.Languages.Mech.instCoeExpr_1 : Coe Val (Expr Var Val FunId) where
  coe v := .val v
