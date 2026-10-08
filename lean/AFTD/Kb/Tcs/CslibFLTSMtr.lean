import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFLTS

/-!
# Cslib.FLTS.mtr

Topic: computability   Node: 71b9d59d99d0

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLTS.mtr`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/FLTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Extended transition function. Implementation note: compared to [Hopcroft2006], the definition consumes the input list of symbols from the left (instead of the right), in order to match the way lists are constructed.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
/-- Extended transition function. Implementation note: compared to [Hopcroft2006], the definition consumes the input list of symbols from the left (instead of the right), in order to match the way lists are constructed. -/
@[scoped grind =]
def Cslib.FLTS.mtr (flts : FLTS State Label) (s : State) (μs : List Label) := μs.foldl flts.tr s
