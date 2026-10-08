import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# TotalPreorder.comparable

Topic: social_choice   Node: 306340a1a7cb

Provenance: formalization of a published result. Source: EconCSLib, `TotalPreorder.comparable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In a total preorder, any two elements are comparable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- In a total preorder, any two elements are comparable. -/
theorem TotalPreorder.comparable [TotalPreorder A] (a b : A) :
    a ≤ b ∨ b ≤ a :=
  TotalPreorder.le_total a b
