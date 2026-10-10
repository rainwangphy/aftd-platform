import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibMultiIndexOrder
import AFTD.Kb.Physics.PhyslibMultiIndex
import AFTD.Kb.Physics.PhyslibMultiIndexInstZero
import AFTD.Kb.Physics.PhyslibMultiIndexZeroApply
import AFTD.Kb.Physics.PhyslibMultiIndexAddApply
import AFTD.Kb.Physics.PhyslibMultiIndexIncrementApplySame
import AFTD.Kb.Physics.PhyslibMultiIndexIncrementApplyNe
import AFTD.Kb.Physics.PhyslibMultiIndexInstCoeFunForallFinNat
import AFTD.Kb.Physics.PhyslibMultiIndexInstAdd

/-!
# Physlib.MultiIndex.order_zero

Topic: classical_mechanics   Node: 0dea7b41f04d

Provenance: formalization of a published result. Source: Physlib, `Physlib.MultiIndex.order_zero`. Lean proof by Juan Jose Fernandez Morales, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/MultiIndex.lean (Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.MultiIndex.order_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.MultiIndex in
open scoped BigOperators in
variable {d : ℕ} in
@[simp]
lemma Physlib.MultiIndex.order_zero : order (0 : MultiIndex d) = 0 := by
  simp [order]
