import AFTD.Prelude

/-!
# IsPreference

Topic: social_choice   Node: 2fc071e8cdbf

Provenance: formalization of a published result. Source: EconCSLib, `IsPreference`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A weak preference relation is admissible if it is reflexive, transitive, and total.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A weak preference relation is admissible if it is reflexive, transitive, and total. -/
class IsPreference {A : Type*} (R : A → A → Prop) : Prop where
  reflexive : Reflexive R
  transitive : Transitive R
  total : ∀ a b : A, R a b ∨ R b a
