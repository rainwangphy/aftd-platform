import AFTD.Prelude

/-!
# VNM.Completeness

Topic: social_choice   Node: b267f25900e8

Provenance: formalization of a published result. Source: EconCSLib, `VNM.Completeness`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Completeness**: every pair is comparable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} in
/-- **Completeness**: every pair is comparable. -/
def VNM.Completeness (pref : A → A → Prop) : Prop :=
  ∀ a b : A, pref a b ∨ pref b a
