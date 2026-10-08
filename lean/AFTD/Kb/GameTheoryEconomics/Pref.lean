import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPreference

/-!
# Pref

Topic: social_choice   Node: ffabea7cdc1f

Provenance: formalization of a published result. Source: EconCSLib, `Pref`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A bundled weak preference relation. Use this interface when several agents may rank the same outcome type differently. Use `[TotalPreorder A]` when the outcome type carries one relevant ambient preference order.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A bundled weak preference relation. Use this interface when several agents may rank the same outcome type differently. Use `[TotalPreorder A]` when the outcome type carries one relevant ambient preference order. -/
structure Pref (A : Type*) where
  rel : A → A → Prop
  prop : IsPreference rel
