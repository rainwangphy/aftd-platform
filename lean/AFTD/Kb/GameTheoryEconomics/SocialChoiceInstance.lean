import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# SocialChoice.Instance

Topic: social_choice   Node: c766a3c43481

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Instance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A generic social-choice instance consists of feasible alternatives together with each agent's preference over the alternative space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A generic social-choice instance consists of feasible alternatives together with each agent's preference over the alternative space. -/
structure SocialChoice.Instance (N A : Type*) where
  /-- Feasible alternatives for this instance. -/
  feasible : A → Prop
  /-- Each agent's weak preference over alternatives. -/
  pref : N → Pref A
