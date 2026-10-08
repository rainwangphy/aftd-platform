import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionContext
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstZeroProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstOneProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstTopProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstBotProposition

/-!
# Cslib.Logic.CLL.Proposition.Context.fill

Topic: proof_theory   Node: 7a8e7ba90575

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.Proposition.Context.fill`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Replaces the hole in a propositional context with a propositions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Replaces the hole in a propositional context with a propositions. -/
@[simp]
def Cslib.Logic.CLL.Proposition.Context.fill (c : Context Atom) (a : Proposition Atom) : Proposition Atom :=
  match c with
  | hole => a
  | tensorL c b => .tensor (c.fill a) b
  | tensorR b c => .tensor b (c.fill a)
  | parrL c b => .parr (c.fill a) b
  | parrR b c => .parr b (c.fill a)
  | oplusL c b => .oplus (c.fill a) b
  | oplusR b c => .oplus b (c.fill a)
  | withL c b => .with (c.fill a) b
  | withR b c => .with b (c.fill a)
  | bang c => .bang (c.fill a)
  | quest c => .quest (c.fill a)
