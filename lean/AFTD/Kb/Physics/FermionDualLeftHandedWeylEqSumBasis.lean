import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualLeftHandedWeyl
import AFTD.Kb.Physics.FermionDualLeftHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionDualLeftHandedWeylInstAddCommGroup
import AFTD.Kb.Physics.FermionDualLeftHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionDualLeftHandedWeylBasis

/-!
# Fermion.DualLeftHandedWeyl.eq_sum_basis

Topic: special_relativity   Node: 4060a3f00c29

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualLeftHandedWeyl.eq_sum_basis`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fermion.DualLeftHandedWeyl.eq_sum_basis
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
lemma Fermion.DualLeftHandedWeyl.eq_sum_basis (ψ : DualLeftHandedWeyl) : ψ = ∑ i, ψ.1 i • basis i := by
  conv_lhs => rw [← basis.sum_repr ψ]
  rfl
