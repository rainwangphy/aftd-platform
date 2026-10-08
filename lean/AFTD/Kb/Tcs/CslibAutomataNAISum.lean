import AFTD.Prelude
import AFTD.Kb.Tcs.CslibAutomataNA
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.Automata.NA.iSum

Topic: automata   Node: cb22246a5a33

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.NA.iSum`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/NA/Sum.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The sum of an indexed family of nondeterministic automata.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Function in
variable {Symbol I : Type*} {State : I → Type*} in
/-- The sum of an indexed family of nondeterministic automata. -/
@[scoped grind =]
def Cslib.Automata.NA.iSum (na : (i : I) → NA (State i) Symbol) : NA (Σ i, State i) Symbol where
  start := ⋃ i, Sigma.mk i '' (na i).start
  Tr s x t := ∃ i s_i t_i, (na i).Tr s_i x t_i ∧ ⟨i, s_i⟩ = s ∧ ⟨i, t_i⟩ = t
