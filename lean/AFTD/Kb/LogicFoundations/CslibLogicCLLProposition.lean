import AFTD.Prelude

/-!
# Cslib.Logic.CLL.Proposition

Topic: proof_theory   Node: 44142bc8cab1

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.Proposition`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Propositions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Propositions. -/
inductive Cslib.Logic.CLL.Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | atomDual (x : Atom)
  | one
  | zero
  | top
  | bot
  /-- The multiplicative conjunction connective. -/
  | tensor (a b : Proposition Atom)
  /-- The multiplicative disjunction connective. -/
  | parr (a b : Proposition Atom)
  /-- The additive disjunction connective. -/
  | oplus (a b : Proposition Atom)
  /-- The additive conjunction connective. -/
  | with (a b : Proposition Atom)
  /-- The "of course" exponential. -/
  | bang (a : Proposition Atom)
  /-- The "why not" exponential.
  This is written as ʔ, or \_?, to distinguish itself from the lean syntatical hole ? syntax -/
  | quest (a : Proposition Atom)
deriving DecidableEq, BEq
