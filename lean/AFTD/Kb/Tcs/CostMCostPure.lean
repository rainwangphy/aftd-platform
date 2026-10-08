import AFTD.Prelude
import AFTD.Kb.Tcs.CostMInstBind
import AFTD.Kb.Tcs.CostMInstSeqRight
import AFTD.Kb.Tcs.CostMInstFunctor
import AFTD.Kb.Tcs.CostMRetPure
import AFTD.Kb.Tcs.CostMInstSeq
import AFTD.Kb.Tcs.CostM
import AFTD.Kb.Tcs.CostMInstPure
import AFTD.Kb.Tcs.CostMInstMonad
import AFTD.Kb.Tcs.CostMInstSeqLeft

/-!
# CostM.cost_pure

Topic: algorithms   Node: 9b8554d2ea1e

Provenance: formalization of a published result. Source: EconCSLib, `CostM.cost_pure`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CostM.cost_pure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {C : Type*} {A B : Type u} in
@[simp] theorem CostM.cost_pure [Zero C] (a : A) : (pure a : CostM C A).cost = 0 := rfl
