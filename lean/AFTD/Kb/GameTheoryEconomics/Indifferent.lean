import AFTD.Prelude

/-!
# Indifferent

Topic: social_choice   Node: 1949e689aee4

Provenance: formalization of a published result. Source: EconCSLib, `Indifferent`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Two outcomes are indifferent under a preorder: `a ≤ b ∧ b ≤ a`. In a `PartialOrder` this implies `a = b`; in a general `Preorder` it does not. [MSZ 2.5]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} [Preorder A] in
/-- Two outcomes are indifferent under a preorder: `a ≤ b ∧ b ≤ a`. In a `PartialOrder` this implies `a = b`; in a general `Preorder` it does not. [MSZ 2.5] -/
def Indifferent (a b : A) : Prop := a ≤ b ∧ b ≤ a
