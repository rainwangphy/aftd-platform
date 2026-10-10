import AFTD.Prelude
import AFTD.Kb.Physics.FermionDirac
import AFTD.Kb.Physics.FermionLeftHandedWeyl
import AFTD.Kb.Physics.FermionDualRightHandedWeyl
import AFTD.Kb.Physics.FermionDiracInstAddCommGroup
import AFTD.Kb.Physics.FermionLeftHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionDualRightHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionDiracInstModuleComplex
import AFTD.Kb.Physics.FermionLeftHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionDualRightHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionDiracDecomposeEquiv
import AFTD.Kb.Physics.FermionDiracLeftAdd
import AFTD.Kb.Physics.FermionDiracDualRightAdd
import AFTD.Kb.Physics.FermionDiracLeftSmul
import AFTD.Kb.Physics.FermionDiracDualRightSmul

/-!
# Fermion.Dirac.decomposeLinEquiv

Topic: special_relativity   Node: 03eab8f3efe7

Provenance: formalization of a published result. Source: Physlib, `Fermion.Dirac.decomposeLinEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Dirac/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The linear equivalence between `Dirac` and `LeftHandedWeyl × DualRightHandedWeyl`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The linear equivalence between `Dirac` and `LeftHandedWeyl × DualRightHandedWeyl`. -/
noncomputable def Fermion.Dirac.decomposeLinEquiv : Dirac ≃ₗ[ℂ] LeftHandedWeyl × DualRightHandedWeyl where
  toEquiv := decomposeEquiv
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
