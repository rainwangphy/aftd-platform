import AFTD.Prelude
import AFTD.Kb.Physics.FermionRightHandedWeyl
import AFTD.Kb.Physics.FermionRightHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionRightHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionRightHandedWeylToFin2CEquiv

/-!
# Fermion.RightHandedWeyl.toFin2ℂ

Topic: special_relativity   Node: 976e2cb2d012

Provenance: formalization of a published result. Source: Physlib, `Fermion.RightHandedWeyl.toFin2ℂ`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/RightHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The underlying element of `Fin 2 → ℂ` of a element in `RightHandedWeyl` defined through the linear equivalence `toFin2ℂEquiv`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The underlying element of `Fin 2 → ℂ` of a element in `RightHandedWeyl` defined through the linear equivalence `toFin2ℂEquiv`. -/
noncomputable abbrev Fermion.RightHandedWeyl.toFin2ℂ (ψ : RightHandedWeyl) := toFin2ℂEquiv ψ
