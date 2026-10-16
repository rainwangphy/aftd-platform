import AFTD.Prelude

/-!
# MatrixMap

Topic: quantum   Node: e03282d6a6a8

Provenance: formalization of a published result. Source: QuantumInfo, `MatrixMap`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Channels/MatrixMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A `MatrixMap` is a linear map between squares matrices of size A to size B, over R.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A `MatrixMap` is a linear map between squares matrices of size A to size B, over R. -/
abbrev MatrixMap (A B R : Type*) [Semiring R] := Matrix A A R →ₗ[R] Matrix B B R
