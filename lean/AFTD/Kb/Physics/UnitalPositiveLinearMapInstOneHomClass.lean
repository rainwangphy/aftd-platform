import AFTD.Prelude
import AFTD.Kb.Physics.UnitalPositiveLinearMap
import AFTD.Kb.Physics.UnitalPositiveLinearMapInstFunLike

/-!
# UnitalPositiveLinearMap.instOneHomClass

Topic: quantum_mechanics   Node: 644c031def21

Provenance: formalization of a published result. Source: Physlib, `UnitalPositiveLinearMap.instOneHomClass`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/Channel/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

UnitalPositiveLinearMap.instOneHomClass
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
instance UnitalPositiveLinearMap.instOneHomClass : OneHomClass (E →ₚ₁[R] F) E F where
  map_one f := f.map_one'
