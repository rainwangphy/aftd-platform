import AFTD.Prelude
import AFTD.Kb.Physics.FermionDirac
import AFTD.Kb.Physics.FermionLeftHandedWeyl
import AFTD.Kb.Physics.FermionDiracInstAddCommGroup
import AFTD.Kb.Physics.FermionDiracInstModuleComplex
import AFTD.Kb.Physics.FermionLeftHandedWeylInstAddCommGroup
import AFTD.Kb.Physics.FermionLeftHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionLeftHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionDiracLeftAdd
import AFTD.Kb.Physics.FermionDiracDualRightAdd

/-!
# Fermion.Dirac.left_smul

Topic: special_relativity   Node: 89b6eaf791e5

Provenance: formalization of a published result. Source: Physlib, `Fermion.Dirac.left_smul`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Dirac/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fermion.Dirac.left_smul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
@[simp]
lemma Fermion.Dirac.left_smul (c : ℂ) (d : Dirac) : (c • d).left = c • d.left := rfl
