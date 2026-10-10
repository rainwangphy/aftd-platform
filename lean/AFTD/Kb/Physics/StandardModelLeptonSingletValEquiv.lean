import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelLeptonSinglet
import AFTD.Kb.Physics.FermionRightHandedWeyl

/-!
# StandardModel.LeptonSinglet.valEquiv

Topic: quantum_field_theory   Node: e76542689f02

Provenance: formalization of a published result. Source: Physlib, `StandardModel.LeptonSinglet.valEquiv`. Lean proof by Nathaneal Sajan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Fermions/LeptonSinglet.lean (Copyright (c) 2026 Nathaneal Sajan. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Identifies a charged-lepton singlet with its underlying Weyl spinor.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Identifies a charged-lepton singlet with its underlying Weyl spinor. -/
def StandardModel.LeptonSinglet.valEquiv : LeptonSinglet ≃ Fermion.RightHandedWeyl where
  toFun := val
  invFun := fun m => ⟨m⟩
