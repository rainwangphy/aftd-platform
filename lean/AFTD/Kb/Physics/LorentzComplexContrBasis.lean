import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrCModule
import AFTD.Kb.Physics.LorentzContrCModuleInstAddCommMonoid
import AFTD.Kb.Physics.LorentzContrCModuleInstModuleComplex
import AFTD.Kb.Physics.LorentzContrCModuleToFin13CEquiv
import AFTD.Kb.Physics.LorentzContrCModuleValAdd
import AFTD.Kb.Physics.LorentzContrCModuleValSmul

/-!
# Lorentz.complexContrBasis

Topic: special_relativity   Node: c67d52ede140

Provenance: formalization of a published result. Source: Physlib, `Lorentz.complexContrBasis`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The standard basis of complex contravariant Lorentz vectors.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The standard basis of complex contravariant Lorentz vectors. -/
noncomputable def Lorentz.complexContrBasis : Basis (Fin 1 ⊕ Fin 3) ℂ ContrℂModule :=
  Basis.ofEquivFun ContrℂModule.toFin13ℂEquiv
