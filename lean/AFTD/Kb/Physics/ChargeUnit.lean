import AFTD.Prelude

/-!
# ChargeUnit

Topic: classical_fields   Node: d7a619b818e6

Provenance: formalization of a published result. Source: Physlib, `ChargeUnit`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Electromagnetism/Charge/ChargeUnit.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The choices of translationally-invariant metrics on the charge-manifold. Such a choice corresponds to a choice of units for charge. This assumes that an orientation has already being picked on the charge manifold.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
/-- The choices of translationally-invariant metrics on the charge-manifold. Such a choice corresponds to a choice of units for charge. This assumes that an orientation has already being picked on the charge manifold. -/
structure ChargeUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val
