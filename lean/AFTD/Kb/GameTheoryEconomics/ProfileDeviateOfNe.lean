import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Profile
import AFTD.Kb.GameTheoryEconomics.Deviate
import AFTD.Kb.GameTheoryEconomics.ProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.ProfileDeviateSame

/-!
# Profile.deviate_of_ne

Topic: social_choice   Node: 9d9da4517fb5

Provenance: formalization of a published result. Source: EconCSLib, `Profile.deviate_of_ne`. Lean proof by xbei, Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Profile.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At any other index, the profile is unchanged.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {S : N → Type*} [DecidableEq N] in
/-- At any other index, the profile is unchanged. -/
@[simp]
theorem Profile.deviate_of_ne (σ : Profile N S) (i : N) (s' : S i) {j : N} (h : j ≠ i) :
    deviate σ i s' j = σ j := by
  simp [deviate, h]
