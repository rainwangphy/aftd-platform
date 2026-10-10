import AFTD.Prelude
import AFTD.Kb.Physics.ComplexLorentzTensorColor
import AFTD.Kb.Physics.RealLorentzTensorInstDecidableEqColor
import AFTD.Kb.Physics.ComplexLorentzTensorInstDecidableEqColor

/-!
# complexLorentzTensor.repDim

Topic: special_relativity   Node: 527f63348dff

Provenance: formalization of a published result. Source: Physlib, `complexLorentzTensor.repDim`. Lean proof by Joseph Tooby-Smith, Nikolai Kashcheev, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The dimensions of each of the different types of complex Lorentz vector space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The dimensions of each of the different types of complex Lorentz vector space. -/
abbrev complexLorentzTensor.repDim (c : Color) : ℕ :=
  match c with
  | Color.upL => 2
  | Color.downL => 2
  | Color.upR => 2
  | Color.downR => 2
  | Color.up => 4
  | Color.down => 4
