import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLanguagesMechPrefix
import AFTD.Kb.Tcs.CslibLanguagesMechExpr
import AFTD.Kb.Tcs.CslibLanguagesMechInstCoeExpr
import AFTD.Kb.Tcs.CslibLanguagesMechInstCoeExpr1

/-!
# Cslib.Languages.Mech.Prefix.pn

Topic: distributed   Node: 2a32b9c4c9df

Provenance: formalization of a published result. Source: CSLib, `Cslib.Languages.Mech.Prefix.pn`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/Choreography/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Process names in a prefix.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable [DecidableEq Pid] in
/-- Process names in a prefix. -/
def Cslib.Languages.Mech.Prefix.pn : Prefix Pid Var Val FunId SelLabel → Finset Pid
  | assign p _ _ => {p}
  | com p _ q _ | sel p q _ => {p, q}
