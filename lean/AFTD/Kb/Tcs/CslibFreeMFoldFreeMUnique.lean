import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMLiftMSeqLeft
import AFTD.Kb.Tcs.CslibFreeMLiftMBind
import AFTD.Kb.Tcs.CslibFreeMFoldFreeMLiftBind
import AFTD.Kb.Tcs.CslibFreeMFoldFreeMLiftBind'
import AFTD.Kb.Tcs.CslibFreeMLiftMSeqRight
import AFTD.Kb.Tcs.CslibFreeMLiftMLift
import AFTD.Kb.Tcs.CslibFreeMLiftMSeq
import AFTD.Kb.Tcs.CslibFreeMFoldFreeMLift
import AFTD.Kb.Tcs.CslibFreeMLiftMMap
import AFTD.Kb.Tcs.CslibFreeM
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMBind
import AFTD.Kb.Tcs.CslibFreeMLift
import AFTD.Kb.Tcs.CslibFreeMFoldFreeM
import AFTD.Kb.Tcs.CslibFreeMInduction
import AFTD.Kb.Tcs.CslibFreeMFoldFreeMPure
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
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad

/-!
# Cslib.FreeM.foldFreeM_unique

Topic: computability   Node: d3462809ab19

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.foldFreeM_unique`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Fold.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Universal Property**: If `h : FreeM F α → β` satisfies: * `h (pure a) = onValue a` * `h ((lift op).bind k) = onEffect op (fun x => h (k x))` then `h` is equal to `foldFreeM onValue onEffect`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' in
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} in
/-- **Universal Property**: If `h : FreeM F α → β` satisfies: * `h (pure a) = onValue a` * `h ((lift op).bind k) = onEffect op (fun x => h (k x))` then `h` is equal to `foldFreeM onValue onEffect`. -/
theorem Cslib.FreeM.foldFreeM_unique
    (onValue : α → β)
    (onEffect : {ι : Type u} → F ι → (ι → β) → β)
    (h : FreeM F α → β)
    (h_pure : ∀ a, h (pure a) = onValue a)
    (h_liftBind : ∀ {ι} (op : F ι) (k : ι → FreeM F α),
      h ((lift op).bind k) = onEffect op (fun x => h (k x))) :
    h = foldFreeM onValue onEffect := by
  funext x
  induction x with
  | pure a =>
    rw [foldFreeM_pure, h_pure]
  | lift_bind op k ih =>
    rw [foldFreeM_lift_bind, h_liftBind]
    grind
