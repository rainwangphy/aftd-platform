import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLanguagesMechChoreography

/-!
# Cslib.Languages.Mech.instZeroChoreography

Topic: distributed   Node: 1168522ab789

Provenance: formalization of a published result. Source: CSLib, `Cslib.Languages.Mech.instZeroChoreography`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/Choreography/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Languages.Mech.instZeroChoreography
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Languages.Mech.instZeroChoreography : Zero (Choreography Pid Var Val FunId SelLabel ProcName) := ⟨.nil⟩
