import AFTD.Prelude
import AFTD.Kb.Tcs.SingularValues

/-!
# singularValues_nonneg

Topic: quantum   Node: aa3846a046b9

Provenance: formalization of a published result. Source: QuantumInfo, `singularValues_nonneg`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Singular values are nonneg.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- Singular values are nonneg. -/
lemma singularValues_nonneg (A : Matrix d d ℂ) (i : d) :
    0 ≤ singularValues A i :=
  Real.sqrt_nonneg _
