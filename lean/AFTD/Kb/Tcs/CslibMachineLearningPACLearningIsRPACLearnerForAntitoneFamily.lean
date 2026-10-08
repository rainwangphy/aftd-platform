import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningConceptClass
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningIsRPACLearnerFor
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLearner
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningError
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningOptimalError

/-!
# Cslib.MachineLearning.PACLearning.IsRPACLearnerFor.antitone_family

Topic: learning   Node: 10ec182d2857

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.IsRPACLearnerFor.antitone_family`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The randomized PAC learner predicate is antitone in the distribution family. The universe of the randomness space `Ω` is pinned so the hypothesis and conclusion share it.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- The randomized PAC learner predicate is antitone in the distribution family. The universe of the randomness space `Ω` is pinned so the hypothesis and conclusion share it. -/
theorem Cslib.MachineLearning.PACLearning.IsRPACLearnerFor.antitone_family.{u} {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : ConceptClass α β} {𝒟 𝒟' : Set (Measure (α × β))}
    (h𝒟 : 𝒟 ⊆ 𝒟') (h : IsRPACLearnerFor.{_, _, u} m ε δ C 𝒟') :
    IsRPACLearnerFor.{_, _, u} m ε δ C 𝒟 := by
  obtain ⟨Ω, mΩ, Q, hQ, A, hA⟩ := h
  exact ⟨Ω, mΩ, Q, hQ, A, fun D inst hD => @hA D inst (h𝒟 hD)⟩
