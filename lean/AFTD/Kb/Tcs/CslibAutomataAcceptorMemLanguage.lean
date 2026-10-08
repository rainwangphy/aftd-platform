import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataAcceptor
import AFTD.Kb.Tcs.CslibAutomataAcceptorLanguage

/-!
# Cslib.Automata.Acceptor.mem_language

Topic: automata   Node: dad9e7286b66

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.Acceptor.mem_language`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/Acceptors/Acceptor.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A string is in the language of an acceptor iff the acceptor accepts it.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {Symbol : Type v} in
/-- A string is in the language of an acceptor iff the acceptor accepts it. -/
@[simp, scoped grind =]
theorem Cslib.Automata.Acceptor.mem_language [Acceptor A Symbol] (a : A) (xs : List Symbol) :
  xs ∈ language a ↔ Accepts a xs := Iff.rfl
