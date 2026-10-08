import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataNA
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.Automata.NA.iProd

Topic: automata   Node: ed7b2420e3d8

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.NA.iProd`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/NA/Prod.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The product of an indexed family of nondeterministic automata.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set List in
variable {Symbol I : Type*} {State : I → Type*} in
/-- The product of an indexed family of nondeterministic automata. -/
@[scoped grind =]
def Cslib.Automata.NA.iProd (na : (i : I) → NA (State i) Symbol) : NA (Π i, State i) Symbol where
  Tr s x t := ∀ i, (na i).Tr (s i) x (t i)
  start := ⋂ i, (· i) ⁻¹' (na i).start
