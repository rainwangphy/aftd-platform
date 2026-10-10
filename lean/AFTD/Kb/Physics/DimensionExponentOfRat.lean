import AFTD.Prelude
import AFTD.Kb.Physics.DimensionExponent
import AFTD.Kb.Physics.DimensionInstReprExponent

/-!
# Dimension.Exponent.ofRat

Topic: classical_mechanics   Node: 44e5f0e09f26

Provenance: formalization of a published result. Source: Physlib, `Dimension.Exponent.ofRat`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Units/Exponent.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Regard a rational number as a dimension exponent.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Regard a rational number as a dimension exponent. -/
def Dimension.Exponent.ofRat (q : ℚ) : Exponent := ⟨q⟩
