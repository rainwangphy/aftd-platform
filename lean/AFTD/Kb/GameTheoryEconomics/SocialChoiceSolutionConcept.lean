import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceInstance

/-!
# SocialChoice.SolutionConcept

Topic: social_choice   Node: f002da86ea76

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.SolutionConcept`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A solution concept is a predicate selecting acceptable alternatives relative to a social-choice instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A solution concept is a predicate selecting acceptable alternatives relative to a social-choice instance. -/
def SocialChoice.SolutionConcept (N A : Type*) :=
  Instance N A → A → Prop
