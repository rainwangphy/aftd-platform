import AFTD.Prelude

/-!
# StrictlyPreferred

Topic: social_choice   Node: 9e15a8587b0d

Provenance: formalization of a published result. Source: EconCSLib, `StrictlyPreferred`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Strict preference is just `<` from the preorder. [MSZ 2.5]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} [Preorder A] in
/-- Strict preference is just `<` from the preorder. [MSZ 2.5] -/
abbrev StrictlyPreferred (a b : A) : Prop := a < b
