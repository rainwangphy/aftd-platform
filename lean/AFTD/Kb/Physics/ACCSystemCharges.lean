import AFTD.Prelude

/-!
# ACCSystemCharges

Topic: quantum_field_theory   Node: c538be72f413

Provenance: formalization of a published result. Source: Physlib, `ACCSystemCharges`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A system of charges, specified by the number of charges.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A system of charges, specified by the number of charges. -/
structure ACCSystemCharges where
  /-- The number of charges. -/
  numberCharges : ℕ
