import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTripartition

/-!
# SocialChoice.Voting.tripartition_lemma

Topic: social_choice   Node: d964e585349f

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.tripartition_lemma`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.tripartition_lemma
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.tripartition_lemma {N : Type*} {A B C : Set N}
    (h : tripartition A B C) :
    ∀ i : N,
      i ∈ A ∪ B ∪ C ∧
      (i ∈ A ↔ i ∉ B ∧ i ∉ C) ∧
      (i ∈ B ↔ i ∉ A ∧ i ∉ C) ∧
      (i ∈ C ↔ i ∉ A ∧ i ∉ B) := by
  intro i
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> by_cases hC : i ∈ C <;>
    simp_all [tripartition]
  · have := Set.mem_inter hA hB; simp_all
  · have := Set.mem_inter hA hB; simp_all
  · have := Set.mem_inter hA hC; simp_all
  · have := Set.mem_inter hB hC; simp_all
  · have hnot : i ∉ A ∪ B ∪ C := by
      intro hmem
      rcases hmem with (hmem | hmem) | hmem <;> contradiction
    rw [h.2.2.2] at hnot
    exact hnot trivial
