import AFTD.Prelude
import AFTD.Kb.Tcs.LinearEquivEuclideanOfRelabel
import AFTD.Kb.Tcs.LinearEquivOfRelabelRefl

/-!
# LinearEquiv.euclideanOfRelabel_refl

Topic: quantum   Node: a73f82a5d47f

Provenance: formalization of a published result. Source: QuantumInfo, `LinearEquiv.euclideanOfRelabel_refl`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/LinearEquiv.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearEquiv.euclideanOfRelabel_refl
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearEquiv in
variable {d d₁ d₂ d₃ R 𝕜 : Type*} [RCLike 𝕜] in
variable {R : Type*} [Semiring R] in
variable (e : d ≃ d₂) in
@[simp]
theorem LinearEquiv.euclideanOfRelabel_refl : euclideanOfRelabel 𝕜 (.refl d) =
    LinearEquiv.refl 𝕜 (EuclideanSpace 𝕜 d) := by
  rfl
