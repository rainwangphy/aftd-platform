import AFTD.Prelude

/-!
# Cslib.Probability.PMF.uniformOfFintype_map_equiv

Topic: randomness   Node: a80b03a425ba

Provenance: formalization of a published result. Source: CSLib, `Cslib.Probability.PMF.uniformOfFintype_map_equiv`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Probability/PMF.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A uniform distribution on a finite type is invariant under any equivalence.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ENNReal in
universe u v in
variable {α : Type u} {β : Type v} in
/-- A uniform distribution on a finite type is invariant under any equivalence. -/
theorem Cslib.Probability.PMF.uniformOfFintype_map_equiv {γ : Type v} [Fintype α] [Fintype γ] [Nonempty α] [Nonempty γ]
    (e : α ≃ γ) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype γ := by
  classical
  have hcard : Fintype.card α = Fintype.card γ := Fintype.card_congr e
  ext c
  rw [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_eq_single (e.symm c)]
  · simp_rw [PMF.uniformOfFintype_apply]
    simp [hcard]
  · intro a ha
    simp_rw [PMF.uniformOfFintype_apply]
    split_ifs with h
    · exfalso
      apply ha
      simpa using congrArg e.symm h.symm
    · simp
