import AFTD.Prelude

/-!
# SpectralMeasure

Topic: quantum_mechanics   Node: fa67fcfc0879

Provenance: formalization of a published result. Source: Physlib, `SpectralMeasure`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/SpectralMeasure.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 2 verbatim; compiled here.

A _spectral measure_ on a measurable space `α` is a σ-additive function `Set α → H →L[ℂ] H` such that each set is mapped to a star projection on `H`, the empty set and non-measurable sets are mapped to zero, and `univ` is mapped to the identity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ContinuousLinearMap in
open MeasureTheory in
open Set in
/-- A _spectral measure_ on a measurable space `α` is a σ-additive function `Set α → H →L[ℂ] H` such that each set is mapped to a star projection on `H`, the empty set and non-measurable sets are mapped to zero, and `univ` is mapped to the identity. -/
structure SpectralMeasure
    (α : Type*) [MeasurableSpace α]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends VectorMeasure α (H →L[ℂ] H) where
  isStarProjection' : ∀ A, IsStarProjection (measureOf' A)
  univ' : measureOf' univ = 1

attribute [coe] SpectralMeasure.toVectorMeasure
