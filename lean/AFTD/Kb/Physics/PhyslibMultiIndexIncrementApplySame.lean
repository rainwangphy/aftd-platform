import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibMultiIndex
import AFTD.Kb.Physics.PhyslibMultiIndexIncrement
import AFTD.Kb.Physics.PhyslibMultiIndexZeroApply
import AFTD.Kb.Physics.PhyslibMultiIndexAddApply
import AFTD.Kb.Physics.PhyslibMultiIndexInstCoeFunForallFinNat
import AFTD.Kb.Physics.PhyslibMultiIndexInstZero
import AFTD.Kb.Physics.PhyslibMultiIndexInstAdd

/-!
# Physlib.MultiIndex.increment_apply_same

Topic: classical_mechanics   Node: 5a812e05071c

Provenance: formalization of a published result. Source: Physlib, `Physlib.MultiIndex.increment_apply_same`. Lean proof by Juan Jose Fernandez Morales, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/MultiIndex.lean (Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.MultiIndex.increment_apply_same
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.MultiIndex in
open scoped BigOperators in
variable {d : ℕ} in
@[simp]
lemma Physlib.MultiIndex.increment_apply_same (I : MultiIndex d) (i : Fin d) :
    increment I i i = I i + 1 := by
  simp [increment]
