import AFTD.Prelude

/-!
# Matrix.reindex_eq_conj

Topic: quantum   Node: 26c50bd7f815

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.reindex_eq_conj`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Isometry.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.reindex_eq_conj
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Matrix in
variable {d d₂ d₃ R : Type*} in
variable [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃] in
variable [CommRing R] [StarRing R] in
variable {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix d d 𝕜} in
omit [Fintype d₂] [DecidableEq d₂] [StarRing R] in
theorem Matrix.reindex_eq_conj (A : Matrix d d R) (e : d ≃ d₂) : reindex e e A =
    (reindex (α := R) e (.refl d) 1) * A * (reindex (α := R) (.refl d) e 1) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.reindex]
  simp [Matrix.one_apply]
