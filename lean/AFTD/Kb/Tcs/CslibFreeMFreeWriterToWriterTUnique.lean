import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMFreeWriter
import AFTD.Kb.Tcs.CslibFreeMInterprets
import AFTD.Kb.Tcs.CslibFreeMWriterF
import AFTD.Kb.Tcs.CslibFreeMFreeWriterWriterInterp
import AFTD.Kb.Tcs.CslibFreeMFreeWriterToWriterT
import AFTD.Kb.Tcs.CslibFreeMInterpretsEq
import AFTD.Kb.Tcs.CslibFreeM
import AFTD.Kb.Tcs.CslibFreeMPureEqPure
import AFTD.Kb.Tcs.CslibFreeMBindEqBind
import AFTD.Kb.Tcs.CslibFreeMMapEqMap
import AFTD.Kb.Tcs.CslibFreeMLiftBindEq
import AFTD.Kb.Tcs.CslibFreeMPureBind
import AFTD.Kb.Tcs.CslibFreeMBindPure
import AFTD.Kb.Tcs.CslibFreeMBindPureComp
import AFTD.Kb.Tcs.CslibFreeMMapPure
import AFTD.Kb.Tcs.CslibFreeMMapBind
import AFTD.Kb.Tcs.CslibFreeMIdMap
import AFTD.Kb.Tcs.CslibFreeMLiftMPure
import AFTD.Kb.Tcs.CslibFreeMLiftMLiftBind
import AFTD.Kb.Tcs.CslibFreeMLiftMLift
import AFTD.Kb.Tcs.CslibFreeMLiftMBind
import AFTD.Kb.Tcs.CslibFreeMLiftMMap
import AFTD.Kb.Tcs.CslibFreeMLiftMSeq
import AFTD.Kb.Tcs.CslibFreeMLiftMSeqLeft
import AFTD.Kb.Tcs.CslibFreeMLiftMSeqRight
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.PFunctorFreeMInterpretsEq

/-!
# Cslib.FreeM.FreeWriter.toWriterT_unique

Topic: computability   Node: fc6eed84aca6

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.FreeWriter.toWriterT_unique`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`toWriterT` is the unique interpreter extending `writerInterp`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.FreeM Cslib.FreeM.FreeWriter in
universe u v w w' w'' in
open WriterF in
variable {ω : Type u} {α β : Type*} in
/-- `toWriterT` is the unique interpreter extending `writerInterp`. -/
theorem Cslib.FreeM.FreeWriter.toWriterT_unique {α : Type u} [Monoid ω] (g : FreeWriter ω α → WriterT ω Id α)
    (h : Interprets writerInterp g) : g = toWriterT := h.eq
