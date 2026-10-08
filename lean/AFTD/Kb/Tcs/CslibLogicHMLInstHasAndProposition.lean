import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicHasAnd
import AFTD.Kb.Tcs.CslibLogicHMLProposition
import AFTD.Kb.Tcs.CslibLogicHMLInstTopProposition

/-!
# Cslib.Logic.HML.instHasAndProposition

Topic: distributed   Node: 40e61fd11b12

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.HML.instHasAndProposition`. Lean proof by Fabrizio Montesi, Marco Peressotti, Alexandre Rademaker, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/HML/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.HML.instHasAndProposition
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Logic.HML.instHasAndProposition : HasAnd (Proposition Label) := ⟨.and⟩
