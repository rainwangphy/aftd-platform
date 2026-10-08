import AFTD.Prelude
import AFTD.Kb.Tcs.CslibRightCongruence
import AFTD.Kb.Tcs.CslibAutomataDA
import AFTD.Kb.Tcs.CslibFLTS

/-!
# Cslib.RightCongruence.toDA

Topic: automata   Node: 4fc5865f1b83

Provenance: formalization of a published result. Source: CSLib, `Cslib.RightCongruence.toDA`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/DA/Congr.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every right congruence gives rise to a DA whose states are the equivalence classes of the right congruence, whose start state is the empty word, and whose transition functiuon is concatenation on the right of the input symbol. Note that the transition function is well-defined only because `c` is a right congruence.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {Symbol : Type*} in
/-- Every right congruence gives rise to a DA whose states are the equivalence classes of the right congruence, whose start state is the empty word, and whose transition functiuon is concatenation on the right of the input symbol. Note that the transition function is well-defined only because `c` is a right congruence. -/
@[scoped grind =]
def Cslib.RightCongruence.toDA [c : RightCongruence Symbol] : Automata.DA (Quotient c.eq) Symbol where
  tr s x := Quotient.lift (fun u ↦ ⟦ u ++ [x] ⟧) (by
    intro u v h_eq
    apply Quotient.sound
    exact right_cov.elim [x] h_eq
  ) s
  start := ⟦ [] ⟧
