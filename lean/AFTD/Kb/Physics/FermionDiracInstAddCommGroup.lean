import AFTD.Prelude
import AFTD.Kb.Physics.FermionDirac
import AFTD.Kb.Physics.FermionLeftHandedWeyl
import AFTD.Kb.Physics.FermionDualRightHandedWeyl
import AFTD.Kb.Physics.FermionDiracDecomposeEquiv
import AFTD.Kb.Physics.FermionLeftHandedWeylInstAddCommGroup
import AFTD.Kb.Physics.FermionDualRightHandedWeylInstAddCommGroup

/-!
# Fermion.Dirac.instAddCommGroup

Topic: special_relativity   Node: b61f06bd12ab

Provenance: formalization of a published result. Source: Physlib, `Fermion.Dirac.instAddCommGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Dirac/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fermion.Dirac.instAddCommGroup
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
noncomputable instance Fermion.Dirac.instAddCommGroup : AddCommGroup Dirac := Equiv.addCommGroup decomposeEquiv
