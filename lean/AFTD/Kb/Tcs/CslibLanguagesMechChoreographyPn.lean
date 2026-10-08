import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLanguagesMechChoreography
import AFTD.Kb.Tcs.CslibLanguagesMechPrefix
import AFTD.Kb.Tcs.CslibLanguagesMechPrefixPn
import AFTD.Kb.Tcs.CslibLanguagesMechExpr
import AFTD.Kb.Tcs.CslibLanguagesMechInstCoeExpr
import AFTD.Kb.Tcs.CslibLanguagesMechInstCoeExpr1
import AFTD.Kb.Tcs.CslibLanguagesMechInstZeroChoreography

/-!
# Cslib.Languages.Mech.Choreography.pn

Topic: distributed   Node: 9d282e419e16

Provenance: formalization of a published result. Source: CSLib, `Cslib.Languages.Mech.Choreography.pn`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/Choreography/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Process names in a choreography.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable [DecidableEq Pid] in
/-- Process names in a choreography. -/
def Cslib.Languages.Mech.Choreography.pn : Choreography Pid Var Val FunId SelLabel ProcName → Finset Pid
  | 0 => ∅
  | pre prf c => prf.pn ∪ c.pn
  | cond p _ c₁ c₂ => {p} ∪ c₁.pn ∪ c₂.pn
  | call _ args => args.toFinset
