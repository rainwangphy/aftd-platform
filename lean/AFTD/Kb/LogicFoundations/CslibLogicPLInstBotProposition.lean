import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicPLProposition

/-!
# Cslib.Logic.PL.instBotProposition

Topic: proof_theory   Node: 94af8c830906

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.PL.instBotProposition`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/Propositional/Defs.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.PL.instBotProposition
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {Atom : Type u} [DecidableEq Atom] in
instance Cslib.Logic.PL.instBotProposition [Bot Atom] : Bot (Proposition Atom) := ⟨.atom ⊥⟩
