import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLogicHMLProposition

/-!
# Cslib.Logic.HML.instTopProposition

Topic: distributed   Node: 31e0875ff9c7

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.HML.instTopProposition`. Lean proof by Fabrizio Montesi, Marco Peressotti, Alexandre Rademaker, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/HML/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.HML.instTopProposition
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Logic.HML.instTopProposition : Top (Proposition Label) := ⟨.true⟩
