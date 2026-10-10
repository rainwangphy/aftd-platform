import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsExt
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# ACCSystemLinear.linSolsAddCommMonoid

Topic: quantum_field_theory   Node: 48cab4b3050f

Provenance: formalization of a published result. Source: Physlib, `ACCSystemLinear.linSolsAddCommMonoid`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An instance providing the operations and properties for `LinSols` to form an additive commutative monoid.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An instance providing the operations and properties for `LinSols` to form an additive commutative monoid. -/
@[simps!]
instance ACCSystemLinear.linSolsAddCommMonoid (χ : ACCSystemLinear) :
    AddCommMonoid χ.LinSols where
  add S T := ⟨S.val + T.val, fun _ ↦ by simp [(χ.linearACCs _).map_add, S.linearSol _,
    T.linearSol _]⟩
  add_comm S T := LinSols.ext (χ.chargesAddCommMonoid.add_comm _ _)
  add_assoc S T L := LinSols.ext (χ.chargesAddCommMonoid.add_assoc _ _ _)
  zero := ⟨χ.chargesAddCommMonoid.zero, fun _ ↦ (χ.linearACCs _).map_zero⟩
  zero_add S := LinSols.ext (χ.chargesAddCommMonoid.zero_add _)
  add_zero S := LinSols.ext (χ.chargesAddCommMonoid.add_zero _)
  nsmul n S := ⟨n • S.val, fun _ ↦ by simp [S.linearSol _]⟩
  nsmul_zero n := LinSols.ext (χ.chargesAddCommMonoid.nsmul_zero _)
  nsmul_succ n S := LinSols.ext (χ.chargesAddCommMonoid.nsmul_succ _ _)
