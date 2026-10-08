import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstZeroProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstOneProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstTopProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstBotProposition

/-!
# Cslib.Logic.CLL.Proposition.Context

Topic: proof_theory   Node: 26b67757894e

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.Proposition.Context`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Propositional contexts (single-hole contexts for propositions).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Propositional contexts (single-hole contexts for propositions). -/
inductive Cslib.Logic.CLL.Proposition.Context (Atom : Type u) : Type u where
  | hole
  | tensorL (c : Context Atom) (b : Proposition Atom)
  | tensorR (a : Proposition Atom) (c : Context Atom)
  | parrL (c : Context Atom) (b : Proposition Atom)
  | parrR (a : Proposition Atom) (c : Context Atom)
  | oplusL (c : Context Atom) (b : Proposition Atom)
  | oplusR (a : Proposition Atom) (c : Context Atom)
  | withL (c : Context Atom) (b : Proposition Atom)
  | withR (a : Proposition Atom) (c : Context Atom)
  | bang (c : Context Atom)
  | quest (c : Context Atom)
deriving DecidableEq, BEq
