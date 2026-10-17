import AFTD.Prelude

/-!
# Matrix.Isometry

Topic: quantum   Node: f33b56b9be50

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.Isometry`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Isometry.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An isometry is a matrix `A` such that `AAᴴ = 1`. Compare with a unitary, which requires `AAᴴ = AᴴA = 1`. It is common to claim that, in a finite-dimensional vector space, a two-sided isometry (`A.Isometry ∧ Aᴴ.Isometry`) must be square and therefore unitary; this is does not work out so well here, since a `Matrix m n R` can be a two-sided isometry, but cannot be a `unitary` since the rows and columns are index by different labels.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Matrix in
variable {d d₂ d₃ R : Type*} in
variable [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃] in
variable [CommRing R] [StarRing R] in
variable {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix d d 𝕜} in
/-- An isometry is a matrix `A` such that `AAᴴ = 1`. Compare with a unitary, which requires `AAᴴ = AᴴA = 1`. It is common to claim that, in a finite-dimensional vector space, a two-sided isometry (`A.Isometry ∧ Aᴴ.Isometry`) must be square and therefore unitary; this is does not work out so well here, since a `Matrix m n R` can be a two-sided isometry, but cannot be a `unitary` since the rows and columns are index by different labels. -/
def Matrix.Isometry (A : Matrix d d₂ R) : Prop :=
  Aᴴ * A = 1
