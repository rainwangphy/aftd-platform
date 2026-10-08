import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionNegative
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstZeroProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstOneProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstTopProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstBotProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstHasContextProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionPositiveDecidable

/-!
# Cslib.Logic.CLL.Proposition.negativeDecidable

Topic: proof_theory   Node: e5ad2577efe7

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.Proposition.negativeDecidable`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Whether a `Proposition` is negative is decidable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Whether a `Proposition` is negative is decidable. -/
instance Cslib.Logic.CLL.Proposition.negativeDecidable (a : Proposition Atom) : Decidable a.negative :=
  a.negative.decEq true
