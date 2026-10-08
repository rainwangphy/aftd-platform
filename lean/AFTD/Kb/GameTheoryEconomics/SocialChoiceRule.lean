import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceInstance

/-!
# SocialChoice.Rule

Topic: social_choice   Node: da8a225aac88

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Rule`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A rule returns a feasible alternative for every instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A rule returns a feasible alternative for every instance. -/
def SocialChoice.Rule (N A : Type*) :=
  (I : Instance N A) → {a : A // I.feasible a}
