import AFTD.Prelude
import AFTD.Kb.Tcs.LinearEquivOfRelabel

/-!
# LinearEquiv.euclideanOfRelabel

Topic: quantum   Node: bf5b07e743c3

Provenance: formalization of a published result. Source: QuantumInfo, `LinearEquiv.euclideanOfRelabel`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/LinearEquiv.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `𝕜`-linear equivalence `EuclideanSpace 𝕜 d₂ ≃ₗ[𝕜] EuclideanSpace 𝕜 d` that relabels the coordinates of a vector along an index equivalence `e : d ≃ d₂`. This is the `EuclideanSpace` analogue of `LinearEquiv.ofRelabel`, obtained by transporting it across the `WithLp` identifications.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearEquiv in
variable {d d₁ d₂ d₃ R 𝕜 : Type*} [RCLike 𝕜] in
variable {R : Type*} [Semiring R] in
variable (e : d ≃ d₂) in
variable (𝕜) in
/-- The `𝕜`-linear equivalence `EuclideanSpace 𝕜 d₂ ≃ₗ[𝕜] EuclideanSpace 𝕜 d` that relabels the coordinates of a vector along an index equivalence `e : d ≃ d₂`. This is the `EuclideanSpace` analogue of `LinearEquiv.ofRelabel`, obtained by transporting it across the `WithLp` identifications. -/
@[simps!]
def LinearEquiv.euclideanOfRelabel (e : d ≃ d₂) : EuclideanSpace 𝕜 d₂ ≃ₗ[𝕜] EuclideanSpace 𝕜 d :=
  (WithLp.linearEquiv 2 𝕜 _).trans ((ofRelabel _ e).trans (WithLp.linearEquiv 2 𝕜 _).symm)
