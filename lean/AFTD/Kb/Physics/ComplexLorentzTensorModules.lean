import AFTD.Prelude
import AFTD.Kb.Physics.ComplexLorentzTensorColor
import AFTD.Kb.Physics.ComplexLorentzTensorRepDim
import AFTD.Kb.Physics.FermionLeftHandedWeyl
import AFTD.Kb.Physics.FermionDualLeftHandedWeyl
import AFTD.Kb.Physics.FermionRightHandedWeyl
import AFTD.Kb.Physics.FermionDualRightHandedWeyl
import AFTD.Kb.Physics.LorentzContrCModule
import AFTD.Kb.Physics.LorentzCoCModule
import AFTD.Kb.Physics.LorentzContrCModuleValAdd
import AFTD.Kb.Physics.LorentzContrCModuleValSmul
import AFTD.Kb.Physics.LorentzCoCModuleValAdd
import AFTD.Kb.Physics.LorentzCoCModuleValSmul
import AFTD.Kb.Physics.RealLorentzTensorInstDecidableEqColor
import AFTD.Kb.Physics.ComplexLorentzTensorInstDecidableEqColor

/-!
# complexLorentzTensor.modules

Topic: special_relativity   Node: 181073cae50d

Provenance: formalization of a published result. Source: Physlib, `complexLorentzTensor.modules`. Lean proof by Joseph Tooby-Smith, Nikolai Kashcheev, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The modules associated with each of the different types of complex Lorentz vector space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The modules associated with each of the different types of complex Lorentz vector space. -/
abbrev complexLorentzTensor.modules : Color → Type
  | Color.upL => Fermion.LeftHandedWeyl
  | Color.downL => Fermion.DualLeftHandedWeyl
  | Color.upR => Fermion.RightHandedWeyl
  | Color.downR => Fermion.DualRightHandedWeyl
  | Color.up => Lorentz.ContrℂModule
  | Color.down => Lorentz.CoℂModule
