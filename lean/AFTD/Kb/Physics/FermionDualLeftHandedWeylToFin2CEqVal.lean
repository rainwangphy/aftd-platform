import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualLeftHandedWeyl
import AFTD.Kb.Physics.FermionDualLeftHandedWeylToFin2C

/-!
# Fermion.DualLeftHandedWeyl.toFin2ℂ_eq_val

Topic: special_relativity   Node: 7eea448f593f

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualLeftHandedWeyl.toFin2ℂ_eq_val`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fermion.DualLeftHandedWeyl.toFin2ℂ_eq_val
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
lemma Fermion.DualLeftHandedWeyl.toFin2ℂ_eq_val (ψ : DualLeftHandedWeyl) : ψ.toFin2ℂ = ψ.val := rfl
