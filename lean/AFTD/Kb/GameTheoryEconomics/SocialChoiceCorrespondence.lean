import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceInstance

/-!
# SocialChoice.Correspondence

Topic: social_choice   Node: 96ae2d85ec36

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Correspondence`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A correspondence is a set-valued choice rule on instances.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A correspondence is a set-valued choice rule on instances. -/
def SocialChoice.Correspondence (N A : Type*) :=
  Instance N A → Set A
