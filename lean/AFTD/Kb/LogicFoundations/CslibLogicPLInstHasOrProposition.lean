import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicHasOr
import AFTD.Kb.LogicFoundations.CslibLogicPLProposition
import AFTD.Kb.LogicFoundations.CslibLogicPLInstBotProposition
import AFTD.Kb.LogicFoundations.CslibLogicPLInstTopProposition
import AFTD.Kb.LogicFoundations.CslibLogicPLInstHasAndProposition

/-!
# Cslib.Logic.PL.instHasOrProposition

Topic: proof_theory   Node: efb3f7d602a0

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.PL.instHasOrProposition`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/Propositional/Defs.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.PL.instHasOrProposition
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {Atom : Type u} [DecidableEq Atom] in
instance Cslib.Logic.PL.instHasOrProposition : HasOr (Proposition Atom) := ⟨.or⟩
