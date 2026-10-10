import AFTD.Prelude
import AFTD.Kb.Physics.FermionDirac
import AFTD.Kb.Physics.FermionLeftHandedWeyl
import AFTD.Kb.Physics.FermionDualRightHandedWeyl

/-!
# Fermion.Dirac.decomposeEquiv

Topic: special_relativity   Node: 2b78977e947b

Provenance: formalization of a published result. Source: Physlib, `Fermion.Dirac.decomposeEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Dirac/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The decomposition of a Dirac fermion into its left handed and dual right handed components.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The decomposition of a Dirac fermion into its left handed and dual right handed components. -/
noncomputable def Fermion.Dirac.decomposeEquiv : Dirac ≃ LeftHandedWeyl × DualRightHandedWeyl where
  toFun d := (d.left, d.dualRight)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
