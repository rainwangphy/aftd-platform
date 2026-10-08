import AFTD.Prelude

/-!
# Cslib.Automata.NA.Buchi.histStart

Topic: automata   Node: 4629867d8ab5

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.NA.Buchi.histStart`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/NA/BuchiInter.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The initial history state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Prod Filter in
variable {Symbol : Type*} {State : Bool → Type*} in
/-- The initial history state. -/
@[scoped grind =, nolint unusedArguments]
def Cslib.Automata.NA.Buchi.histStart (_ : Π i, State i) : Bool := false
