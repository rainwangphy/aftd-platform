import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Execution

Topic: computability   Node: 10374165fb69

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Execution`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Execution.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

`Execution` extends `MTr` by providing the intermediate states of a multistep transition.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib in
variable {State Label : Type*} {lts : LTS State Label} in
/-- `Execution` extends `MTr` by providing the intermediate states of a multistep transition. -/
@[grind =]
def Cslib.LTS.Execution (lts : LTS State Label) (s1 : State) (μs : List Label) (s2 : State)
    (ss : List State) : Prop :=
  ∃ _ : ss.length = μs.length + 1, ss[0] = s1 ∧ ss[ss.length - 1] = s2 ∧
  ∀ k, {_ : k < μs.length} → lts.Tr ss[k] μs[k] ss[k + 1]
