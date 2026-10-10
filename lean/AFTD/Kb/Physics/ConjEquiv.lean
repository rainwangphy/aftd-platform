import AFTD.Prelude
import AFTD.Kb.Physics.ConjModule
import AFTD.Kb.Physics.ConjModuleInstAddCommGroup
import AFTD.Kb.Physics.ConjModuleInstModule

/-!
# conjEquiv

Topic: classical_mechanics   Node: 3c27ceb4695f

Provenance: formalization of a published result. Source: Physlib, `conjEquiv`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Modules/ConjModule.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The canonical conjugate-linear equivalence `M ≃ₛₗ[starRingEnd k] ConjModule M`, the identity on the underlying additive group.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
variable {k : Type*} [CommRing k] [StarRing k] in
variable {M : Type*} [AddCommGroup M] [Module k M] in
/-- The canonical conjugate-linear equivalence `M ≃ₛₗ[starRingEnd k] ConjModule M`, the identity on the underlying additive group. -/
def conjEquiv : M ≃ₛₗ[starRingEnd k] ConjModule M where
  toFun v := v
  map_add' _ _ := rfl
  map_smul' r v := by show (r • v : M) = (star (star r) • v : M); rw [star_star]
  invFun v := v
  left_inv _ := rfl
  right_inv _ := rfl
