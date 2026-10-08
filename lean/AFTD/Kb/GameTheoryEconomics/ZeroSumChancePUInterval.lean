import AFTD.Prelude

/-!
# ZeroSumChance.PUInterval

Topic: equilibria   Node: b7884b85bd00

Provenance: formalization of a published result. Source: EconCSLib, `ZeroSumChance.PUInterval`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ZeroSumGameTreeWithChance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Coerce a rational `a` to the unit-interval subtype, defaulting to `⟨0, …⟩` if `a ∉ [0, 1]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Coerce a rational `a` to the unit-interval subtype, defaulting to `⟨0, …⟩` if `a ∉ [0, 1]`. -/
def ZeroSumChance.PUInterval (a : ℚ) : Set.Icc (0 : ℚ) 1 :=
  if h : 0 ≤ a ∧ a ≤ 1 then ⟨a, h⟩ else ⟨0, le_refl _, zero_le_one⟩
