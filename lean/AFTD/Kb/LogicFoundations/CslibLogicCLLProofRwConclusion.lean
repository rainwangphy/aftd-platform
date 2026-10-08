import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLSequent
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystem
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystemDefault
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstHasInferenceSystemSequent
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystemRwConclusion
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
import AFTD.Kb.LogicFoundations.CslibLogicCLLProof

/-!
# Cslib.Logic.CLL.Proof.rwConclusion

Topic: proof_theory   Node: ee3f20ed7aa3

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.Proof.rwConclusion`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Convenience definition for rewriting conclusions in proofs.
-/

set_option quotPrecheck false
open Cslib Cslib.Logic Cslib.Logic.InferenceSystem
@[inherit_doc] local notation S:90 "⇓" a:90 => InferenceSystem.derivation S a
open Cslib Cslib.Logic Cslib.Logic.InferenceSystem
@[inherit_doc] local notation "⇓" a:90 => InferenceSystem.derivation Default a

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib.Logic Cslib.Logic.InferenceSystem in
/-- Convenience definition for rewriting conclusions in proofs. -/
@[grind =]
def Cslib.Logic.CLL.Proof.rwConclusion {Γ Δ : Sequent Atom} (h : Γ = Δ) (p : ⇓Γ) := InferenceSystem.rwConclusion h p
