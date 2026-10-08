import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataNABuchiInterAcc

/-!
# Cslib.Automata.NA.Buchi.histTrans

Topic: automata   Node: c8ffebbf5701

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.NA.Buchi.histTrans`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/NA/BuchiInter.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The transition function of the history state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Prod Filter in
variable {Symbol : Type*} {State : Bool → Type*} in
open scoped Classical in
/-- The transition function of the history state. -/
@[scoped grind =, nolint unusedArguments]
noncomputable def Cslib.Automata.NA.Buchi.histTrans (acc : (i : Bool) → Set (State i))
    (s : (Π i, State i) × Bool) (_ : Symbol) (_ : Π i, State i) : Bool :=
  if s ∈ interAcc false acc then true else
  if s ∈ interAcc true acc then false else s.snd
