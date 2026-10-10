import AFTD.Prelude

/-!
# PureU1.split_equal

Topic: quantum_field_theory   Node: e38426fd47d8

Provenance: formalization of a published result. Source: Physlib, `PureU1.split_equal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/QED/AnomalyCancellation/VectorLike.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a natural number `n`, this lemma proves that `n + n` is equal to `2 * n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
open BigOperators in
variable {n : ℕ} in
/-- Given a natural number `n`, this lemma proves that `n + n` is equal to `2 * n`. -/
lemma PureU1.split_equal (n : ℕ) : n + n = 2 * n := (Nat.two_mul n).symm
