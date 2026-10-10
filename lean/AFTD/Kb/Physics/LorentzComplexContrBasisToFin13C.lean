import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrCModuleToFin13C
import AFTD.Kb.Physics.LorentzContrCModule
import AFTD.Kb.Physics.LorentzContrCModuleInstAddCommMonoid
import AFTD.Kb.Physics.LorentzContrCModuleInstModuleComplex
import AFTD.Kb.Physics.LorentzComplexContrBasis
import AFTD.Kb.Physics.LorentzContrCModuleToFin13CEquiv
import AFTD.Kb.Physics.LorentzContrCModuleValAdd
import AFTD.Kb.Physics.LorentzContrCModuleValSmul

/-!
# Lorentz.complexContrBasis_toFin13ℂ

Topic: special_relativity   Node: 89e86ad498c7

Provenance: formalization of a published result. Source: Physlib, `Lorentz.complexContrBasis_toFin13ℂ`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.complexContrBasis_toFin13ℂ
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
@[simp]
lemma Lorentz.complexContrBasis_toFin13ℂ (i :Fin 1 ⊕ Fin 3) :
    (complexContrBasis i).toFin13ℂ = Pi.single i 1 := by
  simp only [complexContrBasis, Basis.coe_ofEquivFun]
  rfl
