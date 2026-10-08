import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMFreeWriter
import AFTD.Kb.Tcs.CslibFreeMFreeWriterListen
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMWriterF
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
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunToStateM
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunPure
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunGet
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunSet
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunBind
import AFTD.Kb.Tcs.CslibFreeMFreeWriterWriterInterp
import AFTD.Kb.Tcs.CslibFreeMFreeWriterTellDef
import AFTD.Kb.Tcs.CslibFreeMFreeWriterRunPure
import AFTD.Kb.Tcs.CslibFreeMFreeWriterRunLiftTell
import AFTD.Kb.Tcs.CslibFreeMFreeWriterRunBind
import AFTD.Kb.Tcs.CslibFreeMFreeWriterRunToWriterT
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad

/-!
# Cslib.FreeM.FreeWriter.listen_pure

Topic: computability   Node: 64f8c02b996e

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.FreeWriter.listen_pure`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.FreeM.FreeWriter.listen_pure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.FreeM Cslib.FreeM.FreeWriter in
universe u v w w' w'' in
open WriterF in
variable {ω : Type u} {α β : Type*} in
@[simp]
lemma Cslib.FreeM.FreeWriter.listen_pure [Monoid ω] (a : α) :
    listen (pure a : FreeWriter ω α) = .pure (a, 1) := rfl
