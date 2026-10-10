import AFTD.Prelude
import AFTD.Kb.Physics.UnitalPositiveLinearMap
import AFTD.Kb.Physics.UnitalPositiveLinearMapInstFunLike

/-!
# UnitalPositiveLinearMap.instLinearMapClass

Topic: quantum_mechanics   Node: 80a815bf2fc0

Provenance: formalization of a published result. Source: Physlib, `UnitalPositiveLinearMap.instLinearMapClass`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/Channel/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

UnitalPositiveLinearMap.instLinearMapClass
-/

set_option quotPrecheck false
set_option hygiene false
local notation:25 E " →ₚ₁[" R:25 "] " F:0 => UnitalPositiveLinearMap R E F
set_option hygiene true

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open UnitalPositiveLinearMap in
variable {R E F : Type*} [Semiring R]
  [AddCommMonoid E] [PartialOrder E] [AddCommMonoid F] [PartialOrder F]
  [Module R E] [Module R F] [One E] [One F] in
instance UnitalPositiveLinearMap.instLinearMapClass : LinearMapClass (E →ₚ₁[R] F) R E F where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smul f.toLinearMap
