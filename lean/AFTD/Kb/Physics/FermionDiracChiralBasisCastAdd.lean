import AFTD.Prelude
import AFTD.Kb.Physics.FermionDirac
import AFTD.Kb.Physics.FermionDiracInstAddCommGroup
import AFTD.Kb.Physics.FermionDiracInstModuleComplex
import AFTD.Kb.Physics.FermionDiracChiralBasis
import AFTD.Kb.Physics.FermionLeftHandedWeyl
import AFTD.Kb.Physics.FermionLeftHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionLeftHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionLeftHandedWeylBasis
import AFTD.Kb.Physics.FermionDualRightHandedWeyl
import AFTD.Kb.Physics.FermionDualRightHandedWeylInstAddCommGroup
import AFTD.Kb.Physics.FermionDualRightHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionDualRightHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionDiracDecomposeLinEquiv
import AFTD.Kb.Physics.FermionDualRightHandedWeylBasis
import AFTD.Kb.Physics.FermionDiracLeftAdd
import AFTD.Kb.Physics.FermionDiracDualRightAdd
import AFTD.Kb.Physics.FermionDiracLeftSmul
import AFTD.Kb.Physics.FermionDiracDualRightSmul

/-!
# Fermion.Dirac.chiralBasis_cast_add

Topic: special_relativity   Node: 5726ef159c04

Provenance: formalization of a published result. Source: Physlib, `Fermion.Dirac.chiralBasis_cast_add`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Dirac/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fermion.Dirac.chiralBasis_cast_add
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open Module in
lemma Fermion.Dirac.chiralBasis_cast_add (i : Fin 2) : chiralBasis (Fin.castAdd 2 i) =
    ⟨LeftHandedWeyl.basis i, 0⟩ := by
  fin_cases i
  all_goals
    simp only [chiralBasis, Nat.reduceAdd, Basis.map_apply, Basis.coe_reindex,
    Function.comp_apply, Basis.prod_apply, LinearMap.coe_inl, LinearMap.coe_inr]
    rfl
