import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# RepresentsPreference

Topic: social_choice   Node: 520f3f5d6e95

Provenance: formalization of a published result. Source: EconCSLib, `RepresentsPreference`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A utility function `u : A → V` represents the preference `≤` on `A` if `a ≤ b ↔ u a ≤ u b`. [MSZ 2.7]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A utility function `u : A → V` represents the preference `≤` on `A` if `a ≤ b ↔ u a ≤ u b`. [MSZ 2.7] -/
structure RepresentsPreference [Preorder A] [Preorder V'] (u : A → V') : Prop where
  /-- The representation property: `a ≤ b ↔ u(a) ≤ u(b)`. -/
  le_iff : ∀ a b : A, a ≤ b ↔ u a ≤ u b
