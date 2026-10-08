import AFTD.Prelude

/-!
# SocialChoice.Voting.exists_three_distinct_of_card_ge_three

Topic: social_choice   Node: f3390f4d1f5f

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.exists_three_distinct_of_card_ge_three`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Arrow.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A finite alternative set with at least three elements contains three distinct alternatives. This local helper packages the cardinality assumption into the witness shape used by the decisive-coalitions proof of Arrow's theorem.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
/-- A finite alternative set with at least three elements contains three distinct alternatives. This local helper packages the cardinality assumption into the witness shape used by the decisive-coalitions proof of Arrow's theorem. -/
theorem SocialChoice.Voting.exists_three_distinct_of_card_ge_three {A : Type*} [Fintype A]
    (hA : Fintype.card A ≥ 3) :
    ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  classical
  let e := Fintype.equivFin A
  refine ⟨e.symm ⟨0, ?_⟩, e.symm ⟨1, ?_⟩, e.symm ⟨2, ?_⟩, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by decide : 0 < 3) hA
  · exact lt_of_lt_of_le (by decide : 1 < 3) hA
  · exact lt_of_lt_of_le (by decide : 2 < 3) hA
  · intro h
    have := congrArg e h
    simp at this
  · intro h
    have := congrArg e h
    simp at this
  · intro h
    have := congrArg e h
    simp at this
