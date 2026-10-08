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
import AFTD.Kb.Tcs.CostMRetPar
import AFTD.Kb.Tcs.CostMCostPar
import AFTD.Kb.Tcs.CostMRetParList
import AFTD.Kb.Tcs.CostMCostParList
import AFTD.Kb.Tcs.CostMParListNil
import AFTD.Kb.Tcs.CostMCostParListCons
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
# CostM.Bounded

Topic: algorithms   Node: 5866d6cbee0d

Provenance: formalization of a published result. Source: EconCSLib, `CostM.Bounded`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The cost of `alg i` is bounded by `bound (size i)` for every input `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {C : Type*} {A B : Type u} in
/-- The cost of `alg i` is bounded by `bound (size i)` for every input `i`. -/
def CostM.Bounded {Input Output : Type*} [LE C]
    (alg : Input → CostM C Output) (size : Input → ℕ) (bound : ℕ → C) : Prop :=
  ∀ i, (alg i).cost ≤ bound (size i)
