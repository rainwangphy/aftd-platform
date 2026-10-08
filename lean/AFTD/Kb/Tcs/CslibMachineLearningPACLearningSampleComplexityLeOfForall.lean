import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearnerModel
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningSampleComplexity

/-!
# Cslib.MachineLearning.PACLearning.sampleComplexity_le_of_forall

Topic: learning   Node: ed2eacce4b29

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.sampleComplexity_le_of_forall`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

General pointwise monotonicity of `sampleComplexity`: if every witness sample size for `(L₁, ε₁, δ₁, C₁, 𝒟₁)` is also a witness for `(L₂, ε₂, δ₂, C₂, 𝒟₂)`, then the latter's sample complexity is at most the former's (provided the former is attained).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- General pointwise monotonicity of `sampleComplexity`: if every witness sample size for `(L₁, ε₁, δ₁, C₁, 𝒟₁)` is also a witness for `(L₂, ε₂, δ₂, C₂, 𝒟₂)`, then the latter's sample complexity is at most the former's (provided the former is attained). -/
theorem Cslib.MachineLearning.PACLearning.sampleComplexity_le_of_forall {L₁ L₂ : LearnerModel α β}
    {ε₁ δ₁ ε₂ δ₂ : Set.Ioo (0 : ℝ≥0) 1} {C₁ C₂ : ConceptClass α β}
    {𝒟₁ 𝒟₂ : Set (Measure (α × β))}
    (hL : ∀ {m : ℕ}, L₁ m ε₁ δ₁ C₁ 𝒟₁ → L₂ m ε₂ δ₂ C₂ 𝒟₂)
    (h : ∃ m, L₁ m ε₁ δ₁ C₁ 𝒟₁) :
    sampleComplexity L₂ C₂ ε₂ δ₂ 𝒟₂ ≤ sampleComplexity L₁ C₁ ε₁ δ₁ 𝒟₁ :=
  Nat.sInf_le (hL (Nat.sInf_mem h))
