import AFTD.Prelude

/-!
# SuperSymmetry.SU5.FieldLabel

Topic: quantum_field_theory   Node: 8fd2fe97fc25

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.FieldLabel`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/FieldLabels.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The types of field present in an SU(5) GUT.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The types of field present in an SU(5) GUT. -/
inductive SuperSymmetry.SU5.FieldLabel | fiveBarHu
  | fiveHu
  | fiveBarHd
  | fiveHd
  | fiveBarMatter
  | fiveMatter
  | tenMatter
deriving DecidableEq
