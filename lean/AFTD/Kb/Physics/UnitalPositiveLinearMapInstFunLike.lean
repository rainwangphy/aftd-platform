import AFTD.Prelude
import AFTD.Kb.Physics.UnitalPositiveLinearMap

/-!
# UnitalPositiveLinearMap.instFunLike

Topic: quantum_mechanics   Node: acef7dd582be

Provenance: formalization of a published result. Source: Physlib, `UnitalPositiveLinearMap.instFunLike`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/Channel/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

UnitalPositiveLinearMap.instFunLike
-/

set_option quotPrecheck false
set_option hygiene false
local notation:25 E " →ₚ₁[" R:25 "] " F:0 => UnitalPositiveLinearMap R E F
set_option hygiene true

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {R E F : Type*} [Semiring R]
  [AddCommMonoid E] [PartialOrder E] [AddCommMonoid F] [PartialOrder F]
  [Module R E] [Module R F] [One E] [One F] in
instance UnitalPositiveLinearMap.instFunLike : FunLike (E →ₚ₁[R] F) E F where
  coe f := f.toFun
  coe_injective _ _ h := UnitalPositiveLinearMap.ext h
