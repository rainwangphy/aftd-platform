import AFTD.Prelude
import AFTD.Kb.Tcs.CostM
import AFTD.Kb.Tcs.CostMInstPure
import AFTD.Kb.Tcs.CostMInstBind
import AFTD.Kb.Tcs.CostMInstFunctor

/-!
# CostM.instSeq

Topic: algorithms   Node: 8463dae97020

Provenance: formalization of a published result. Source: EconCSLib, `CostM.instSeq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CostM.instSeq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {C : Type*} {A B : Type u} in
instance CostM.instSeq [Add C] : Seq (CostM C) where
  seq f x := ⟨f.ret (x ()).ret, f.cost + (x ()).cost⟩
