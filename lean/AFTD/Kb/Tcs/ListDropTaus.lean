import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasTau
import AFTD.Kb.Tcs.CslibDecidableEqTau

/-!
# List.dropTaus

Topic: automata   Node: 0e11f9025c49

Provenance: formalization of a published result. Source: CSLib, `List.dropTaus`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/NA/EpsilonTransducer.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Removes all `τ`s from a list.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib in
/-- Removes all `τ`s from a list. -/
@[grind =]
def List.dropTaus [HasTau α] [DecidableEqTau α] (l : List α) : List α :=
  l.filter (· ≠ HasTau.τ)
