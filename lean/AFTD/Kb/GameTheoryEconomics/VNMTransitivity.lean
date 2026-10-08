import AFTD.Prelude

/-!
# VNM.Transitivity

Topic: social_choice   Node: a8f0bdb3501a

Provenance: formalization of a published result. Source: EconCSLib, `VNM.Transitivity`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Transitivity**: preference chains compose.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} in
/-- **Transitivity**: preference chains compose. -/
def VNM.Transitivity (pref : A → A → Prop) : Prop :=
  ∀ a b c : A, pref a b → pref b c → pref a c
