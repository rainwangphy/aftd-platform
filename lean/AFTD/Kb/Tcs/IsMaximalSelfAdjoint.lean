import AFTD.Prelude

/-!
# IsMaximalSelfAdjoint

Topic: quantum   Node: ff8375b32b7b

Provenance: formalization of a published result. Source: QuantumInfo, `IsMaximalSelfAdjoint`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/IsMaximalSelfAdjoint.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`IsMaximalSelfAdjoint R α` witnesses that `R` is the maximal `TrivialStar` subring of the star ring `α`, via an additive map `selfadjMap : α →+ R` collecting the self-adjoint part of each element. This lets `HermitianMat.trace` return `𝕜` when `𝕜` already has a trivial star, and the "clean" underlying type otherwise, e.g. `ℝ` when the input field is `ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- `IsMaximalSelfAdjoint R α` witnesses that `R` is the maximal `TrivialStar` subring of the star ring `α`, via an additive map `selfadjMap : α →+ R` collecting the self-adjoint part of each element. This lets `HermitianMat.trace` return `𝕜` when `𝕜` already has a trivial star, and the "clean" underlying type otherwise, e.g. `ℝ` when the input field is `ℂ`. -/
class IsMaximalSelfAdjoint (R : outParam Type*) (α : Type*) [Star α] [Star R] [CommSemiring R]
    [Semiring α] [TrivialStar R] [Algebra R α] where
  /-- The additive map sending an element of `α` to its self-adjoint part in `R`. -/
  selfadjMap : α →+ R
  /-- `selfadjMap` pulls scalar multiplication by `R` out of its argument. -/
  selfadj_smul : ∀ (r : R) (a : α), selfadjMap (r • a) = r * (selfadjMap a)
  /-- On self-adjoint elements, `selfadjMap` is a section of `algebraMap R α`. -/
  selfadj_algebra : ∀ {a : α}, IsSelfAdjoint a → algebraMap _ _ (selfadjMap a) = a
