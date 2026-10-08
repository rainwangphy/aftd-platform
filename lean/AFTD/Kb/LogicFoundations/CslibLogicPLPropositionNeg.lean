import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicPLProposition
import AFTD.Kb.LogicFoundations.CslibLogicPLInstBotProposition

/-!
# Cslib.Logic.PL.Proposition.neg

Topic: proof_theory   Node: 1b3cd7323593

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.PL.Proposition.neg`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/Propositional/Defs.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

We view negation as a defined connective ~A := A → ⊥
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {Atom : Type u} [DecidableEq Atom] in
/-- We view negation as a defined connective ~A := A → ⊥ -/
abbrev Cslib.Logic.PL.Proposition.neg [Bot Atom] : Proposition Atom → Proposition Atom := (Proposition.imp · ⊥)
