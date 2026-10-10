import AFTD.Prelude
import AFTD.Kb.Physics.RealLorentzTensorColor

/-!
# realLorentzTensor.instDecidableEqColor

Topic: special_relativity   Node: dc289cd9e746

Provenance: formalization of a published result. Source: Physlib, `realLorentzTensor.instDecidableEqColor`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Color for real Lorentz tensors is decidable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open TensorProduct in
/-- Color for real Lorentz tensors is decidable. -/
instance realLorentzTensor.instDecidableEqColor : DecidableEq Color := fun x y =>
  match x, y with
  | Color.up, Color.up => isTrue rfl
  | Color.down, Color.down => isTrue rfl
  /- The false -/
  | Color.up, Color.down => isFalse fun h => Color.noConfusion h
  | Color.down, Color.up => isFalse fun h => Color.noConfusion h
