import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibDerivativeIndex
import AFTD.Kb.Physics.PhyslibMultiIndex
import AFTD.Kb.Physics.PhyslibMultiIndexOrder
import AFTD.Kb.Physics.PhyslibMultiIndexZeroApply
import AFTD.Kb.Physics.PhyslibMultiIndexAddApply
import AFTD.Kb.Physics.PhyslibMultiIndexIncrementApplySame
import AFTD.Kb.Physics.PhyslibMultiIndexIncrementApplyNe
import AFTD.Kb.Physics.PhyslibMultiIndexOrderZero
import AFTD.Kb.Physics.PhyslibMultiIndexOrderSingle
import AFTD.Kb.Physics.PhyslibMultiIndexOrderIncrement
import AFTD.Kb.Physics.PhyslibMultiIndexTailZero
import AFTD.Kb.Physics.PhyslibMultiIndexTailIncrementZero
import AFTD.Kb.Physics.PhyslibMultiIndexTailIncrementSucc
import AFTD.Kb.Physics.PhyslibMultiIndexToListZero
import AFTD.Kb.Physics.PhyslibMultiIndexToListIncrementZero
import AFTD.Kb.Physics.PhyslibMultiIndexToListSingle
import AFTD.Kb.Physics.PhyslibMultiIndexInstCoeFunForallFinNat
import AFTD.Kb.Physics.PhyslibMultiIndexInstZero
import AFTD.Kb.Physics.PhyslibMultiIndexInstAdd
import AFTD.Kb.Physics.PhyslibInstFintypeDerivativeIndex

/-!
# Physlib.instDecidableEqDerivativeIndex

Topic: classical_mechanics   Node: ac314ccc4a5f

Provenance: formalization of a published result. Source: Physlib, `Physlib.instDecidableEqDerivativeIndex`. Lean proof by Juan Jose Fernandez Morales, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/DerivativeIndex.lean (Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.instDecidableEqDerivativeIndex
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Physlib.instDecidableEqDerivativeIndex (d k : ℕ) : DecidableEq (DerivativeIndex d k) := inferInstance
