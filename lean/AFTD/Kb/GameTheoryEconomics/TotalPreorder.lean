import AFTD.Prelude

/-!
# TotalPreorder

Topic: social_choice   Node: 36ac012feeb2

Provenance: formalization of a published result. Source: EconCSLib, `TotalPreorder`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A total preorder: a preorder where `≤` is total (complete). This is weaker than `LinearOrder` — it does NOT require antisymmetry or decidable equality. Two distinct elements can be indifferent. This is the appropriate notion for weak preferences in utility theory and matching theory. [MSZ 2.1–2.4]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A total preorder: a preorder where `≤` is total (complete). This is weaker than `LinearOrder` — it does NOT require antisymmetry or decidable equality. Two distinct elements can be indifferent. This is the appropriate notion for weak preferences in utility theory and matching theory. [MSZ 2.1–2.4] -/
class TotalPreorder (A : Type*) extends Preorder A where
  /-- The preference relation is complete: for any `a b`, either `a ≤ b` or `b ≤ a`. -/
  le_total : ∀ (a b : A), a ≤ b ∨ b ≤ a
