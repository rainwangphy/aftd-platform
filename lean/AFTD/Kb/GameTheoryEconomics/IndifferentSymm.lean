import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Indifferent

/-!
# Indifferent.symm

Topic: social_choice   Node: dcb5d3609243

Provenance: formalization of a published result. Source: EconCSLib, `Indifferent.symm`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Indifference is symmetric.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} [Preorder A] in
/-- Indifference is symmetric. -/
theorem Indifferent.symm {a b : A} (h : Indifferent a b) : Indifferent b a := ⟨h.2, h.1⟩
