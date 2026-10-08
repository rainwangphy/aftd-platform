import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringStackTape
import AFTD.Kb.Tcs.CslibTuringStackTapeEmptyEqNil
import AFTD.Kb.Tcs.CslibTuringStackTapeNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeConsNoneNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeConsSomeToList
import AFTD.Kb.Tcs.CslibTuringStackTapeHeadCons
import AFTD.Kb.Tcs.CslibTuringStackTapeTailCons
import AFTD.Kb.Tcs.CslibTuringStackTapeConsHeadTail
import AFTD.Kb.Tcs.CslibTuringStackTapeLengthMapSome
import AFTD.Kb.Tcs.CslibTuringStackTapeLengthNil
import AFTD.Kb.Tcs.CslibTuringStackTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringStackTapeInstEmptyCollection

/-!
# Cslib.Turing.BiTape

Topic: algorithms   Node: 95ce874a80fe

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.BiTape`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/BiTape.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A structure for bidirectionally-infinite Turing machine tapes that eventually take on blank `none` values
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A structure for bidirectionally-infinite Turing machine tapes that eventually take on blank `none` values -/
structure Cslib.Turing.BiTape (Symbol : Type*) where
  /-- The symbol currently under the tape head -/
  head : Option Symbol
  /-- The contents to the left of the head -/
  left : StackTape Symbol
  /-- The contents to the right of the head -/
  right : StackTape Symbol
