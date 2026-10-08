import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMReaderF

/-!
# Cslib.FreeM.FreeReader.readInterp

Topic: computability   Node: b5fdcf5757f7

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.FreeReader.readInterp`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Interpret `ReaderF` operations into `ReaderM`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {σ : Type u} {α : Type u} in
/-- Interpret `ReaderF` operations into `ReaderM`. -/
@[simp]
def Cslib.FreeM.FreeReader.readInterp {α : Type u} : ReaderF σ α → ReaderM σ α | .read => MonadReaderOf.read
