import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasHContext
import AFTD.Kb.LogicFoundations.CslibLogicCLLSequent
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLSequentContext
import AFTD.Kb.LogicFoundations.CslibLogicCLLSequentContextFill
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionContextFill
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstZeroProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstOneProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstTopProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstBotProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstHasContextProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionPositiveDecidable
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionNegativeDecidable

/-!
# Cslib.Logic.CLL.instHasHContextSequentProposition

Topic: proof_theory   Node: 3862a2e8cd39

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.instHasHContextSequentProposition`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.CLL.instHasHContextSequentProposition
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Logic.CLL.instHasHContextSequentProposition : HasHContext (Sequent Atom) (Proposition Atom) := ⟨Sequent.Context.fill⟩
