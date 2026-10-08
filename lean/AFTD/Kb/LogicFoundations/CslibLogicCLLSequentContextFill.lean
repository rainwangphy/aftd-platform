import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstBotProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionPositiveDecidable
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstZeroProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstOneProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstHasContextProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLSequentContext
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstTopProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionNegativeDecidable

/-!
# Cslib.Logic.CLL.Sequent.Context.fill

Topic: proof_theory   Node: 7566b67f65d0

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.Sequent.Context.fill`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Filling a judgemental context returns a sequent.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Filling a judgemental context returns a sequent. -/
def Cslib.Logic.CLL.Sequent.Context.fill (Γc : Sequent.Context Atom) (a : Proposition Atom) := a ::ₘ Γc
