import AFTD.Prelude
import AFTD.Kb.Physics.FermionDirac
import AFTD.Kb.Physics.FermionLeftHandedWeyl
import AFTD.Kb.Physics.FermionDiracInstAddCommGroup
import AFTD.Kb.Physics.FermionLeftHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionDiracInstModuleComplex

/-!
# Fermion.Dirac.left_add

Topic: special_relativity   Node: dac67643980d

Provenance: formalization of a published result. Source: Physlib, `Fermion.Dirac.left_add`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Dirac/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fermion.Dirac.left_add
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
@[simp]
lemma Fermion.Dirac.left_add (d₁ d₂ : Dirac) : (d₁ + d₂).left = d₁.left + d₂.left := rfl
