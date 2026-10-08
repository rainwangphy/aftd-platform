import AFTD.Prelude
import AFTD.Kb.Tcs.CostM
import AFTD.Kb.Tcs.CostMRetPure
import AFTD.Kb.Tcs.CostMRetBind
import AFTD.Kb.Tcs.CostMRetMap
import AFTD.Kb.Tcs.CostMRetSeqLeft
import AFTD.Kb.Tcs.CostMRetSeqRight
import AFTD.Kb.Tcs.CostMRetSeq
import AFTD.Kb.Tcs.CostMCostPure
import AFTD.Kb.Tcs.CostMCostBind
import AFTD.Kb.Tcs.CostMCostMap
import AFTD.Kb.Tcs.CostMCostSeqLeft
import AFTD.Kb.Tcs.CostMCostSeqRight
import AFTD.Kb.Tcs.CostMCostSeq
import AFTD.Kb.Tcs.CostMRetTick
import AFTD.Kb.Tcs.CostMCostTick
import AFTD.Kb.Tcs.CostMInstPure
import AFTD.Kb.Tcs.CostMInstBind
import AFTD.Kb.Tcs.CostMInstFunctor
import AFTD.Kb.Tcs.CostMInstSeq
import AFTD.Kb.Tcs.CostMInstSeqLeft
import AFTD.Kb.Tcs.CostMInstSeqRight
import AFTD.Kb.Tcs.CostMInstMonad
import AFTD.Kb.Tcs.CostMInstLawfulMonad
import AFTD.Kb.Tcs.CostMInstCoeHead

/-!
# CostM.par

Topic: algorithms   Node: eeab142daa73

Provenance: formalization of a published result. Source: EconCSLib, `CostM.par`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Independent (parallel) composition of two `CostM` computations. The return is the pair of return values; the cost is the sup of the two costs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {C : Type*} {A B : Type u} in
/-- Independent (parallel) composition of two `CostM` computations. The return is the pair of return values; the cost is the sup of the two costs. -/
def CostM.par [SemilatticeSup C] (m₁ : CostM C A) (m₂ : CostM C B) : CostM C (A × B) :=
  ⟨(m₁.ret, m₂.ret), m₁.cost ⊔ m₂.cost⟩
