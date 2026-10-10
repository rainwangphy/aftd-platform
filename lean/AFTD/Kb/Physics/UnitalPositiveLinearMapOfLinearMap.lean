import AFTD.Prelude
import AFTD.Kb.Physics.UnitalPositiveLinearMap

/-!
# UnitalPositiveLinearMap.ofLinearMap

Topic: quantum_mechanics   Node: 0647cf95c56d

Provenance: formalization of a published result. Source: Physlib, `UnitalPositiveLinearMap.ofLinearMap`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/Channel/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Bundle a linear map after proving only positivity and preservation of `1`.
-/

set_option quotPrecheck false
set_option hygiene false
local notation:25 E " →ₚ₁[" R:25 "] " F:0 => UnitalPositiveLinearMap R E F
set_option hygiene true

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {R E F : Type*} [Semiring R]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [AddCommGroup F] [PartialOrder F] [IsOrderedAddMonoid F]
  [Module R E] [Module R F] [One E] [One F] in
/-- Bundle a linear map after proving only positivity and preservation of `1`. -/
def UnitalPositiveLinearMap.ofLinearMap (f : E →ₗ[R] F) (hpos : ∀ x, 0 ≤ x → 0 ≤ f x) (hone : f 1 = 1) : E →ₚ₁[R] F where
  toPositiveLinearMap := PositiveLinearMap.mk₀ f hpos
  map_one' := hone
