import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLSequent
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
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

/-!
# Cslib.Logic.CLL.Sequent.allQuest

Topic: proof_theory   Node: 09249dca6d84

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.Sequent.allQuest`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Checks that all propositions in a sequent `Γ` are question marks.
-/

open Cslib.Logic.CLL
@[inherit_doc] local infix:35 " ⊗ " => Proposition.tensor
@[inherit_doc] local infix:35 " ⊕ " => Proposition.oplus
@[inherit_doc] local infix:30 " ⅋ " => Proposition.parr
@[inherit_doc] local infix:30 " & " => Proposition.with
@[inherit_doc] local prefix:95 "!" => Proposition.bang
@[inherit_doc] local prefix:95 "ʔ" => Proposition.quest

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Checks that all propositions in a sequent `Γ` are question marks. -/
def Cslib.Logic.CLL.Sequent.allQuest (Γ : Sequent Atom) :=
  Γ.map (· matches ʔ_)
  |> Multiset.fold Bool.and true
