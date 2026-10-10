import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibMultiIndex
import AFTD.Kb.Physics.PhyslibMultiIndexInstCoeFunForallFinNat
import AFTD.Kb.Physics.PhyslibMultiIndexInstZero
import AFTD.Kb.Physics.PhyslibMultiIndexInstAdd

/-!
# Physlib.MultiIndex.increment

Topic: classical_mechanics   Node: 994b51aa2798

Provenance: formalization of a published result. Source: Physlib, `Physlib.MultiIndex.increment`. Lean proof by Juan Jose Fernandez Morales, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Derivatives/MultiIndex.lean (Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Increment the `i`-th coordinate of a multi-index by one.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib in
open scoped BigOperators in
variable {d : ℕ} in
/-- Increment the `i`-th coordinate of a multi-index by one. -/
def Physlib.MultiIndex.increment (I : MultiIndex d) (i : Fin d) : MultiIndex d := ⟨I.toFun + Pi.single i 1⟩
