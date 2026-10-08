import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicPLProposition
import AFTD.Kb.LogicFoundations.CslibLogicPLInstBotProposition

/-!
# Cslib.Logic.PL.Proposition.top

Topic: proof_theory   Node: 68faeef18084

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.PL.Proposition.top`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/Propositional/Defs.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A fixed choice of a derivable proposition (of course any two are equivalent).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {Atom : Type u} [DecidableEq Atom] in
/-- A fixed choice of a derivable proposition (of course any two are equivalent). -/
abbrev Cslib.Logic.PL.Proposition.top [Inhabited Atom] : Proposition Atom := imp (.atom default) (.atom default)
