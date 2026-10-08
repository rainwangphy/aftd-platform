import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataAcceptor

/-!
# Cslib.Automata.Acceptor.language

Topic: automata   Node: 6ca7f06b55df

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.Acceptor.language`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/Acceptors/Acceptor.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The language of an `Acceptor` is the set of strings it `Accepts`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {Symbol : Type v} in
/-- The language of an `Acceptor` is the set of strings it `Accepts`. -/
@[scoped grind .]
def Cslib.Automata.Acceptor.language [Acceptor A Symbol] (a : A) : Language Symbol :=
  { xs | Accepts a xs }
