import AFTD.Prelude
import AFTD.Kb.Physics.FermionRightHandedWeyl

/-!
# StandardModel.LeptonSinglet

Topic: quantum_field_theory   Node: 75dfb714711e

Provenance: formalization of a published result. Source: Physlib, `StandardModel.LeptonSinglet`. Lean proof by Nathaneal Sajan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Fermions/LeptonSinglet.lean (Copyright (c) 2026 Nathaneal Sajan. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The target vector space of one Standard Model charged-lepton singlet. It carries the `(1, 1)_{-6}` representation of the gauge group.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The target vector space of one Standard Model charged-lepton singlet. It carries the `(1, 1)_{-6}` representation of the gauge group. -/
@[ext]
structure StandardModel.LeptonSinglet where
  /-- The right-handed Weyl spinor. -/
  val : Fermion.RightHandedWeyl
