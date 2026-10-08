import AFTD.Prelude
import AFTD.Kb.Tcs.CostM
import AFTD.Kb.Tcs.CostMInstPure

/-!
# CostM.bind

Topic: algorithms   Node: 04161fa2d9f9

Provenance: formalization of a published result. Source: EconCSLib, `CostM.bind`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Sequential composition. The cost of `m >>= f` is `m.cost + (f m.ret).cost`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {C : Type*} {A B : Type u} in
/-- Sequential composition. The cost of `m >>= f` is `m.cost + (f m.ret).cost`. -/
protected def CostM.bind [Add C] (m : CostM C A) (f : A → CostM C B) : CostM C B :=
  let r := f m.ret
  ⟨r.ret, m.cost + r.cost⟩
