import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixTraceNorm
import AFTD.Kb.Tcs.MatrixIsometry
import AFTD.Kb.Tcs.MatrixMemUnitaryGroupIffIsometry
import AFTD.Kb.Tcs.MatrixTraceNormIsometryConj
import AFTD.Kb.Tcs.MatrixTraceNormZero
import AFTD.Kb.Tcs.MatrixTraceNormNeg

/-!
# Matrix.traceNorm_unitary_conj

Topic: quantum   Node: 5ef017acbc0d

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.traceNorm_unitary_conj`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The trace norm is invariant under unitary conjugation.
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
open MatrixOrder Isometry in
/-- The trace norm is invariant under unitary conjugation. -/
@[simp]
theorem Matrix.traceNorm_unitary_conj {A : Matrix n n R} {U : Matrix.unitaryGroup n R} :
  traceNorm (U.val * A * U.valᴴ) = traceNorm A := by
  have hu := (Matrix.mem_unitaryGroup_iff_isometry U.val).mp U.2
  exact traceNorm_isometry_conj hu.1 hu.1
