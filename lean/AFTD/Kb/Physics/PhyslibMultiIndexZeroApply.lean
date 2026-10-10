import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibMultiIndex
import AFTD.Kb.Physics.PhyslibMultiIndexInstZero
import AFTD.Kb.Physics.PhyslibMultiIndexInstCoeFunForallFinNat
import AFTD.Kb.Physics.PhyslibMultiIndexInstAdd

/-!
# Physlib.MultiIndex.zero_apply

Topic: classical_mechanics   Node: a29fde2f4b30

Provenance: formalization of a published result. Source: Physlib, `Physlib.MultiIndex.zero_apply`. Lean proof by Juan Jose Fernandez Morales, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/MultiIndex.lean (Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.MultiIndex.zero_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.MultiIndex in
open scoped BigOperators in
variable {d : ℕ} in
@[simp]
lemma Physlib.MultiIndex.zero_apply (i : Fin d) : (0 : MultiIndex d) i = 0 := rfl
