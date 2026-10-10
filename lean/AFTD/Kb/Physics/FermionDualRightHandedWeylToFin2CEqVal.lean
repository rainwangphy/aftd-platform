import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualRightHandedWeyl
import AFTD.Kb.Physics.FermionDualRightHandedWeylToFin2C

/-!
# Fermion.DualRightHandedWeyl.toFin2ℂ_eq_val

Topic: special_relativity   Node: 7ce9814602d5

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualRightHandedWeyl.toFin2ℂ_eq_val`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualRightHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fermion.DualRightHandedWeyl.toFin2ℂ_eq_val
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
lemma Fermion.DualRightHandedWeyl.toFin2ℂ_eq_val (ψ : DualRightHandedWeyl) : ψ.toFin2ℂ = ψ.val := rfl
