import AFTD.Prelude
import AFTD.Kb.Tcs.CostM
import AFTD.Kb.Tcs.CostMInstBind
import AFTD.Kb.Tcs.CostMInstPure
import AFTD.Kb.Tcs.CostMInstFunctor
import AFTD.Kb.Tcs.CostMInstSeq
import AFTD.Kb.Tcs.CostMInstSeqLeft
import AFTD.Kb.Tcs.CostMInstSeqRight
import AFTD.Kb.Tcs.CostMInstMonad

/-!
# CostM.ret_bind

Topic: algorithms   Node: 132710c5ae85

Provenance: formalization of a published result. Source: EconCSLib, `CostM.ret_bind`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CostM.ret_bind
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {C : Type*} {A B : Type u} in
@[simp] theorem CostM.ret_bind [Add C] (m : CostM C A) (f : A → CostM C B) :
    (m >>= f).ret = (f m.ret).ret := rfl
