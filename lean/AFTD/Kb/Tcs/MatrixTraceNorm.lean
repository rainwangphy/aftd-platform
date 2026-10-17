import AFTD.Prelude

/-!
# Matrix.traceNorm

Topic: quantum   Node: 39e4f5cad76c

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.traceNorm`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The trace norm of a matrix: Tr[√(A† A)].
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
open Classical in
open scoped ComplexOrder in
variable {m n R : Type*} in
variable [Fintype m] [Fintype n] in
variable [RCLike R] in
/-- The trace norm of a matrix: Tr[√(A† A)]. -/
noncomputable def Matrix.traceNorm (A : Matrix m n R) : ℝ :=
  open MatrixOrder in
  RCLike.re (CFC.sqrt (Aᴴ * A)).trace
