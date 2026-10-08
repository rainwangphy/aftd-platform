import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMFreeReader
import AFTD.Kb.Tcs.CslibFreeMFreeReaderInstMonadReaderOf
import AFTD.Kb.Tcs.CslibFreeMLift
import AFTD.Kb.Tcs.CslibFreeMReaderF
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
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunGet
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunSet
import AFTD.Kb.Tcs.CslibFreeMFreeStateRun'Get
import AFTD.Kb.Tcs.CslibFreeMFreeStateRun'Set
import AFTD.Kb.Tcs.CslibFreeMFreeWriterRunLiftTell
import AFTD.Kb.Tcs.CslibFreeMFreeWriterListenLiftTellBind
import AFTD.Kb.Tcs.CslibFreeMFreeContRunLiftCallCC
import AFTD.Kb.Tcs.CslibFreeMFreeContRunCallCC
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad
import AFTD.Kb.Tcs.PFunctorFreeMLift

/-!
# Cslib.FreeM.FreeReader.read_def

Topic: computability   Node: 4640d5f75eec

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.FreeReader.read_def`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.FreeM.FreeReader.read_def
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.FreeM Cslib.FreeM.FreeReader in
universe u v w w' w'' in
variable {σ : Type u} {α : Type u} in
lemma Cslib.FreeM.FreeReader.read_def : (read : FreeReader σ σ) = .lift .read := rfl
