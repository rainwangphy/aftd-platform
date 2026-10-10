import AFTD.Prelude

/-!
# PureU1.VectorLikeOddPlane.odd_shift_eq

Topic: quantum_field_theory   Node: 07e254fbd3ca

Provenance: formalization of a published result. Source: Physlib, `PureU1.VectorLikeOddPlane.odd_shift_eq`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/QED/AnomalyCancellation/Odd/BasisLinear.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PureU1.VectorLikeOddPlane.odd_shift_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Nat Finset BigOperators in
variable {n : ℕ} in
lemma PureU1.VectorLikeOddPlane.odd_shift_eq (n : ℕ) : (1 + n) + n = 2 * n +1 := by
  omega
