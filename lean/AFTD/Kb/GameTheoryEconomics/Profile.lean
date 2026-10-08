import AFTD.Prelude

/-!
# Profile

Topic: social_choice   Node: 15c50f7b3759

Provenance: formalization of a published result. Source: EconCSLib, `Profile`. Lean proof by xbei, Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Profile.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A strategy profile: a dependent function assigning a value to each index. Compatibility alias only. Prefer game-bound profile aliases such as `G.Profile`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A strategy profile: a dependent function assigning a value to each index. Compatibility alias only. Prefer game-bound profile aliases such as `G.Profile`. -/
abbrev Profile (N : Type*) (S : N → Type*) := ∀ i : N, S i
