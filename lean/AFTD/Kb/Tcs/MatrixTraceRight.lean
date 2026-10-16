import AFTD.Prelude

/-!
# Matrix.traceRight

Topic: quantum   Node: eeab9c29759e

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.traceRight`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.traceRight
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
variable [AddCommMonoid R] [Fintype d] in
noncomputable def Matrix.traceRight (m : Matrix (d₁ × d) (d₂ × d) R) : Matrix d₁ d₂ R :=
  Matrix.of fun i₂ j₂ ↦ ∑ i₁, m (i₂, i₁) (j₂, i₁)
