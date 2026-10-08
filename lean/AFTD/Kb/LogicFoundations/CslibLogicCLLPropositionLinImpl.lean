import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDual
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
# Cslib.Logic.CLL.Proposition.linImpl

Topic: proof_theory   Node: 4eceb3a5c89f

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.Proposition.linImpl`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Linear implication.
-/

open Cslib.Logic.CLL
@[inherit_doc] local infix:35 " ⊗ " => Proposition.tensor
@[inherit_doc] local infix:35 " ⊕ " => Proposition.oplus
@[inherit_doc] local infix:30 " ⅋ " => Proposition.parr
@[inherit_doc] local infix:30 " & " => Proposition.with
@[inherit_doc] local prefix:95 "!" => Proposition.bang
@[inherit_doc] local prefix:95 "ʔ" => Proposition.quest
open Cslib.Logic.CLL
@[inherit_doc] local postfix:max "⫠" => Proposition.dual

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Linear implication. -/
@[scoped grind =]
def Cslib.Logic.CLL.Proposition.linImpl (a b : Proposition Atom) : Proposition Atom := a⫠ ⅋ b
