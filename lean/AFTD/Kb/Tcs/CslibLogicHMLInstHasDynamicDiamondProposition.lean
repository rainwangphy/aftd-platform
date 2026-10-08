import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicHasDynamicDiamond
import AFTD.Kb.Tcs.CslibLogicHMLProposition
import AFTD.Kb.Tcs.CslibLogicHMLInstTopProposition
import AFTD.Kb.Tcs.CslibLogicHMLInstHasAndProposition
import AFTD.Kb.Tcs.CslibLogicHMLInstHasNotProposition

/-!
# Cslib.Logic.HML.instHasDynamicDiamondProposition

Topic: distributed   Node: 8f16b5acb930

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.HML.instHasDynamicDiamondProposition`. Lean proof by Fabrizio Montesi, Marco Peressotti, Alexandre Rademaker, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/HML/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.HML.instHasDynamicDiamondProposition
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Logic.HML.instHasDynamicDiamondProposition : HasDynamicDiamond (Proposition Label) Label := ⟨.diamond⟩
