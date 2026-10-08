import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstBotProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionContext
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
import AFTD.Kb.Tcs.CslibHasContext
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstZeroProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstOneProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionContextFill
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstTopProposition
import AFTD.Kb.Tcs.CslibHasHContext

/-!
# Cslib.Logic.CLL.instHasContextProposition

Topic: proof_theory   Node: 7596183ad623

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.instHasContextProposition`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.CLL.instHasContextProposition
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Logic.CLL.instHasContextProposition : HasContext (Proposition Atom) := ⟨Proposition.Context.fill⟩
