import AFTD.Prelude
import AFTD.Kb.Physics.UnitalPositiveLinearMap

/-!
# UnitalPositiveLinearMap.toPositiveLinearMap_injective

Topic: quantum_mechanics   Node: c936142317d2

Provenance: formalization of a published result. Source: Physlib, `UnitalPositiveLinearMap.toPositiveLinearMap_injective`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/Channel/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Unital positive linear maps are determined by their underlying positive linear map.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {R E F : Type*} [Semiring R]
  [AddCommMonoid E] [PartialOrder E] [AddCommMonoid F] [PartialOrder F]
  [Module R E] [Module R F] [One E] [One F] in
/-- Unital positive linear maps are determined by their underlying positive linear map. -/
lemma UnitalPositiveLinearMap.toPositiveLinearMap_injective :
    Function.Injective (toPositiveLinearMap (R := R) (E := E) (F := F)) :=
  fun _ _ h ↦ by ext x; congrm($h x)
