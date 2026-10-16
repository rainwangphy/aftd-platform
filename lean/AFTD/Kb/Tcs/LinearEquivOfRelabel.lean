import AFTD.Prelude

/-!
# LinearEquiv.ofRelabel

Topic: quantum   Node: cb3c3f926f21

Provenance: formalization of a published result. Source: QuantumInfo, `LinearEquiv.ofRelabel`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/LinearEquiv.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `R`-linear equivalence `(d₂ → R) ≃ₗ[R] (d → R)` that relabels the coordinates of a function along an index equivalence `e : d ≃ d₂`. This is the linear-equivalence packaging of `Equiv.piCongrLeft`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {d d₁ d₂ d₃ R 𝕜 : Type*} [RCLike 𝕜] in
variable {R : Type*} [Semiring R] in
variable (R) in
/-- The `R`-linear equivalence `(d₂ → R) ≃ₗ[R] (d → R)` that relabels the coordinates of a function along an index equivalence `e : d ≃ d₂`. This is the linear-equivalence packaging of `Equiv.piCongrLeft`. -/
@[simps]
def LinearEquiv.ofRelabel (e : d ≃ d₂) : (d₂ → R) ≃ₗ[R] (d → R) := by
  refine' { e.symm.piCongrLeft (fun _ ↦ R) with .. }
  <;> (intros; ext; simp [Equiv.piCongrLeft_apply])
