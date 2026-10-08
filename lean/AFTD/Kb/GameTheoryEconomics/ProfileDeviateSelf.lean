import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Profile
import AFTD.Kb.GameTheoryEconomics.Deviate

/-!
# Profile.deviate_self

Topic: social_choice   Node: e7aefe70a958

Provenance: formalization of a published result. Source: EconCSLib, `Profile.deviate_self`. Lean proof by xbei, Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Profile.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Deviating to the same value is the identity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {S : N → Type*} [DecidableEq N] in
/-- Deviating to the same value is the identity. -/
@[simp]
theorem Profile.deviate_self (σ : Profile N S) (i : N) :
    deviate σ i (σ i) = σ := by
  simp [deviate]
