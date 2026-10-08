import AFTD.Prelude

/-!
# Cslib.Automata.Transducer

Topic: automata   Node: 4c0b711fb73b

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.Transducer`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/Transducers/Transducer.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A `Transducer` is an automaton that translates strings (lists of symbols, from an input to an output alphabet).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A `Transducer` is an automaton that translates strings (lists of symbols, from an input to an output alphabet). -/
class Cslib.Automata.Transducer (A : Type u) (InSymbol OutSymbol : outParam (Type v)) where
  /-- The string `xs` can be translated into `ys` by `a`. -/
  Translates (a : A) (xs : List InSymbol) (ys : List OutSymbol) : Prop
