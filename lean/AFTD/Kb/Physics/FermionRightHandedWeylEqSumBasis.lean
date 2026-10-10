import AFTD.Prelude
import AFTD.Kb.Physics.FermionRightHandedWeyl
import AFTD.Kb.Physics.FermionRightHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionRightHandedWeylInstAddCommGroup
import AFTD.Kb.Physics.FermionRightHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionRightHandedWeylBasis

/-!
# Fermion.RightHandedWeyl.eq_sum_basis

Topic: special_relativity   Node: c31907d65fa2

Provenance: formalization of a published result. Source: Physlib, `Fermion.RightHandedWeyl.eq_sum_basis`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/RightHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fermion.RightHandedWeyl.eq_sum_basis
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
lemma Fermion.RightHandedWeyl.eq_sum_basis (ψ : RightHandedWeyl) : ψ = ∑ i, ψ.1 i • basis i := by
  conv_lhs => rw [← basis.sum_repr ψ]
  rfl
