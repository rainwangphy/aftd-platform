import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibMultiIndex
import AFTD.Kb.Physics.PhyslibMultiIndexInstCoeFunForallFinNat

/-!
# Physlib.MultiIndex.instZero

Topic: classical_mechanics   Node: 1f4572ea6d60

Provenance: formalization of a published result. Source: Physlib, `Physlib.MultiIndex.instZero`. Lean proof by Juan Jose Fernandez Morales, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/MultiIndex.lean (Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.MultiIndex.instZero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib in
open scoped BigOperators in
variable {d : ℕ} in
instance Physlib.MultiIndex.instZero : Zero (MultiIndex d) := ⟨⟨0⟩⟩
