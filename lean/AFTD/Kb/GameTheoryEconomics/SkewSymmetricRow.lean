import AFTD.Prelude

/-!
# SkewSymmetric.Row

Topic: equilibria   Node: 45c92d6effb8

Provenance: formalization of a published result. Source: EconCSLib, `SkewSymmetric.Row`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/SkewSymmetric.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Row index of the feasibility system `z S ≥ 0, z ≥ 0, ∑ z = 1`: `inl l` = the column constraint `(zS)_l ≥ 0`; `inr (inl k)` = `z_k ≥ 0`; `inr (inr false/true)` = `∑ z ≥ 1` / `∑ (−z) ≥ −1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {N : ℕ} in
/-- Row index of the feasibility system `z S ≥ 0, z ≥ 0, ∑ z = 1`: `inl l` = the column constraint `(zS)_l ≥ 0`; `inr (inl k)` = `z_k ≥ 0`; `inr (inr false/true)` = `∑ z ≥ 1` / `∑ (−z) ≥ −1`. -/
abbrev SkewSymmetric.Row (N : ℕ) := Fin N ⊕ Fin N ⊕ Bool
