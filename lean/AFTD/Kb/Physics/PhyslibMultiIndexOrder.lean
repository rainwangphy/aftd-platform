import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibMultiIndex
import AFTD.Kb.Physics.PhyslibMultiIndexInstCoeFunForallFinNat
import AFTD.Kb.Physics.PhyslibMultiIndexInstZero
import AFTD.Kb.Physics.PhyslibMultiIndexInstAdd

/-!
# Physlib.MultiIndex.order

Topic: classical_mechanics   Node: 2d3ae008ec79

Provenance: formalization of a published result. Source: Physlib, `Physlib.MultiIndex.order`. Lean proof by Juan Jose Fernandez Morales, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/MultiIndex.lean (Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The order `|I|` of a multi-index `I`, defined as the sum of its components.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib in
open scoped BigOperators in
variable {d : ℕ} in
/-- The order `|I|` of a multi-index `I`, defined as the sum of its components. -/
def Physlib.MultiIndex.order (I : MultiIndex d) : Nat := ∑ i, I i
