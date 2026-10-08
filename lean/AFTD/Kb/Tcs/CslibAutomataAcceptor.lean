import AFTD.Prelude

/-!
# Cslib.Automata.Acceptor

Topic: automata   Node: 5fba565074d0

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.Acceptor`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/Acceptors/Acceptor.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An `Acceptor` is a machine that recognises strings (lists of symbols in an alphabet).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An `Acceptor` is a machine that recognises strings (lists of symbols in an alphabet). -/
class Cslib.Automata.Acceptor (A : Type u) (Symbol : outParam (Type v)) where
  /-- Predicate that establishes whether a string `xs` is accepted. -/
  Accepts (a : A) (xs : List Symbol) : Prop
