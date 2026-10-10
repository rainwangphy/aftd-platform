import AFTD.Prelude
import AFTD.Kb.Physics.FermionLeftHandedWeyl
import AFTD.Kb.Physics.FermionLeftHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionLeftHandedWeylToFin2CFun

/-!
# Fermion.LeftHandedWeyl.toFin2ℂAddEquiv

Topic: special_relativity   Node: da0ee8663902

Provenance: formalization of a published result. Source: Physlib, `Fermion.LeftHandedWeyl.toFin2ℂAddEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/LeftHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The additive equivalence between `LeftHandedWeyl` and `Fin 2 → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The additive equivalence between `LeftHandedWeyl` and `Fin 2 → ℂ`. -/
noncomputable def Fermion.LeftHandedWeyl.toFin2ℂAddEquiv : LeftHandedWeyl ≃+ (Fin 2 → ℂ) :=
  { toFin2ℂFun with map_add' _ _ := rfl }
