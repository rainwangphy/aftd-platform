import AFTD.Prelude
import AFTD.Kb.Tcs.CostM
import AFTD.Kb.Tcs.CostMInstPure
import AFTD.Kb.Tcs.CostMInstBind

/-!
# CostM.instFunctor

Topic: algorithms   Node: 5fcbd58ebc2c

Provenance: formalization of a published result. Source: EconCSLib, `CostM.instFunctor`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CostM.instFunctor
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {C : Type*} {A B : Type u} in
instance CostM.instFunctor : Functor (CostM C) where
  map f x := ⟨f x.ret, x.cost⟩
