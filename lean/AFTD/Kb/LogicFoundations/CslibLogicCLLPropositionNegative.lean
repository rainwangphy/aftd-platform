import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstZeroProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstOneProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstTopProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstBotProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstHasContextProposition

/-!
# Cslib.Logic.CLL.Proposition.negative

Topic: proof_theory   Node: 98b55febf7e7

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.Proposition.negative`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Negative propositions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Negative propositions. -/
def Cslib.Logic.CLL.Proposition.negative : Proposition Atom → Bool
  | atomDual _ | bot | top | parr _ _ | .with _ _ | quest _ => true
  | _ => false
