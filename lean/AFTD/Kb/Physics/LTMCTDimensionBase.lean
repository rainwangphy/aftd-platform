import AFTD.Prelude

/-!
# LTMCTDimensionBase

Topic: classical_mechanics   Node: 1379faea1f8c

Provenance: formalization of a published result. Source: Physlib, `LTMCTDimensionBase`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/LTMCTDimensionBase.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PhysLib's default basis of base dimensions — `length`, `time`, `mass`, `charge`, `temperature`. Note this is *charge*-based, so it is not the SI/ISQ base-quantity set; see `Dimension`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- PhysLib's default basis of base dimensions — `length`, `time`, `mass`, `charge`, `temperature`. Note this is *charge*-based, so it is not the SI/ISQ base-quantity set; see `Dimension`. -/
inductive LTMCTDimensionBase where
  /-- The length base dimension. -/
  | length
  /-- The time base dimension. -/
  | time
  /-- The mass base dimension. -/
  | mass
  /-- The charge base dimension. -/
  | charge
  /-- The temperature base dimension. -/
  | temperature
deriving DecidableEq
