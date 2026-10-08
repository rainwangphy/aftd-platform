import AFTD.Prelude

/-!
# Cslib.Logic.PL.Proposition

Topic: proof_theory   Node: 2b64fa96010b

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.PL.Proposition`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/Propositional/Defs.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Propositions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {Atom : Type u} [DecidableEq Atom] in
/-- Propositions. -/
inductive Cslib.Logic.PL.Proposition (Atom : Type u) : Type u where
  /-- Propositional atoms -/
  | atom (x : Atom)
  /-- Conjunction -/
  | and (a b : Proposition Atom)
  /-- Disjunction -/
  | or (a b : Proposition Atom)
  /-- Implication -/
  | imp (a b : Proposition Atom)
deriving DecidableEq, BEq
