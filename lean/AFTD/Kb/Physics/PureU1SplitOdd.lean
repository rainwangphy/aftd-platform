import AFTD.Prelude

/-!
# PureU1.split_odd

Topic: quantum_field_theory   Node: 8ca7e9896098

Provenance: formalization of a published result. Source: Physlib, `PureU1.split_odd`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/QED/AnomalyCancellation/VectorLike.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PureU1.split_odd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
open BigOperators in
variable {n : ℕ} in
lemma PureU1.split_odd (n : ℕ) : n + 1 + n = 2 * n + 1 := by omega
