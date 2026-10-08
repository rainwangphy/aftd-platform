import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDual
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDualInvolution
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystem
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystemDefault
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstHasInferenceSystemSequent
import AFTD.Kb.LogicFoundations.CslibLogicCLLProof
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDualSizeOf
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDualInj
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstZeroProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstOneProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstTopProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstBotProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstHasContextProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionPositiveDecidable
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionNegativeDecidable
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstHasHContextSequentProposition

/-!
# Cslib.Logic.CLL.Proof.cut'

Topic: proof_theory   Node: 5d98bd93d05b

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.Proof.cut'`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Cut, but where the premises are reversed.
-/

set_option quotPrecheck false
open Cslib Cslib.Logic Cslib.Logic.CLL
@[inherit_doc] local postfix:max "⫠" => Proposition.dual
open Cslib Cslib.Logic Cslib.Logic.InferenceSystem
@[inherit_doc] local notation S:90 "⇓" a:90 => InferenceSystem.derivation S a
open Cslib Cslib.Logic Cslib.Logic.InferenceSystem
@[inherit_doc] local notation "⇓" a:90 => InferenceSystem.derivation Default a

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib.Logic Cslib.Logic.InferenceSystem in
/-- Cut, but where the premises are reversed. -/
@[grind =]
def Cslib.Logic.CLL.Proof.cut' (p : ⇓(a⫠ ::ₘ Γ)) (q : ⇓(a ::ₘ Δ)) : ⇓(Γ + Δ) :=
  let r : ⇓(a⫠⫠ ::ₘ Δ) := (Proposition.dual_involution a).symm ▸ q
  p.cut r
