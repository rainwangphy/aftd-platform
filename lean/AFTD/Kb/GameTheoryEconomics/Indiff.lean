import AFTD.Prelude

/-!
# indiff

Topic: social_choice   Node: 91f109946c4f

Provenance: formalization of a published result. Source: EconCSLib, `indiff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Indifference derived from a weak preference relation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Indifference derived from a weak preference relation. -/
def indiff {A : Type*} (R : A → A → Prop) (a b : A) : Prop :=
  R a b ∧ R b a
