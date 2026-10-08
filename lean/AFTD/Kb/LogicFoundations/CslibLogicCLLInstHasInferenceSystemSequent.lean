import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicHasInferenceSystem
import AFTD.Kb.LogicFoundations.CslibLogicCLLSequent
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystem
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystemDefault
import AFTD.Kb.LogicFoundations.CslibLogicCLLProof
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDualSizeOf
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDualInj
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDualInvolution
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstZeroProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstOneProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstTopProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstBotProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstHasContextProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionPositiveDecidable
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionNegativeDecidable
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstHasHContextSequentProposition

/-!
# Cslib.Logic.CLL.instHasInferenceSystemSequent

Topic: proof_theory   Node: 3ea59281a096

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.instHasInferenceSystemSequent`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.CLL.instHasInferenceSystemSequent
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib.Logic Cslib.Logic.InferenceSystem in
instance Cslib.Logic.CLL.instHasInferenceSystemSequent : HasInferenceSystem (Sequent Atom) := ⟨Proof⟩
