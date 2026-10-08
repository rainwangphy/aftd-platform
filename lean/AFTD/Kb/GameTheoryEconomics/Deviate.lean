import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# deviate

Topic: social_choice   Node: 20ca268f2323

Provenance: formalization of a published result. Source: EconCSLib, `deviate`. Lean proof by xbei, Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Profile.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Unilateral deviation: index `i` switches to `s'`, all others keep their value. This is `Function.update` with a game-theoretic name.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Unilateral deviation: index `i` switches to `s'`, all others keep their value. This is `Function.update` with a game-theoretic name. -/
abbrev deviate {N : Type*} {S : N → Type*} [DecidableEq N]
    (σ : Profile N S) (i : N) (s' : S i) : Profile N S :=
  Function.update σ i s'
