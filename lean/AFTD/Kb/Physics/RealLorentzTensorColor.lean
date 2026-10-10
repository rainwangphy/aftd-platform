import AFTD.Prelude

/-!
# realLorentzTensor.Color

Topic: special_relativity   Node: cde2887609c6

Provenance: formalization of a published result. Source: Physlib, `realLorentzTensor.Color`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The colors associated with real representations of O(1, 3) of interest to physics.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open TensorProduct in
set_option backward.isDefEq.respectTransparency false in
/-- The colors associated with real representations of O(1, 3) of interest to physics. -/
inductive realLorentzTensor.Color
  /-- The color associated with contravariant Lorentz vectors. -/ | up : Color
  /-- The color associated with covariant Lorentz vectors. -/
  | down : Color
deriving Fintype
