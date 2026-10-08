import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionContext
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
import AFTD.Kb.Tcs.CslibHasHContext
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstHasContextProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionContextFill
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstZeroProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstOneProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstTopProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstBotProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLSequentContextFill

/-!
# Cslib.Logic.CLL.Proposition.context_fill_def

Topic: proof_theory   Node: 7ebea2319f97

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.Proposition.context_fill_def`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Definition of context filling.
-/

open Cslib
@[inherit_doc] local notation:max c "<[" t "]" => HasHContext.fill c t

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Definition of context filling. -/
@[scoped grind =]
theorem Cslib.Logic.CLL.Proposition.context_fill_def (c : Context Atom) (a : Proposition Atom) :
  c<[a] = c.fill a := rfl
