import AFTD.Prelude

/-!
# PureU1.ConstAbsProp

Topic: quantum_field_theory   Node: 4331a50d7d04

Provenance: formalization of a published result. Source: Physlib, `PureU1.ConstAbsProp`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/QED/AnomalyCancellation/ConstAbs.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The condition for two rationals to have the same square (equivalent to same abs).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
open BigOperators in
variable {n : ℕ} in
/-- The condition for two rationals to have the same square (equivalent to same abs). -/
def PureU1.ConstAbsProp : ℚ × ℚ → Prop := fun s => s.1^2 = s.2^2
