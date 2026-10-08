import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstTopProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDual
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstZeroProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstOneProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstBotProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstHasContextProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionPositiveDecidable
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionNegativeDecidable

/-!
# Cslib.Logic.CLL.Proposition.top_eq_zero_dual

Topic: proof_theory   Node: 5b3da6dfc56e

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.Proposition.top_eq_zero_dual`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.CLL.Proposition.top_eq_zero_dual
-/

open Cslib.Logic.CLL
@[inherit_doc] local postfix:max "⫠" => Proposition.dual

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[scoped grind =]
theorem Cslib.Logic.CLL.Proposition.top_eq_zero_dual : ⊤ = (0⫠ : Proposition Atom) := rfl
