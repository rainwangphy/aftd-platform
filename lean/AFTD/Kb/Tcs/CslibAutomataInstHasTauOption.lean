import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasTau

/-!
# Cslib.Automata.instHasTauOption

Topic: automata   Node: 6802346c1f87

Provenance: formalization of a published result. Source: CSLib, `Cslib.Automata.instHasTauOption`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Automata/EpsilonNA/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Automata.instHasTauOption
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Symbol : Type*} in
@[local grind =]
instance Cslib.Automata.instHasTauOption : HasTau (Option α) := ⟨.none⟩
