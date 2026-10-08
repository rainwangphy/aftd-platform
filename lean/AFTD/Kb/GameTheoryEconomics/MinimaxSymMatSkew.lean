import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxSymMat

/-!
# Minimax.symMat_skew

Topic: equilibria   Node: b6be71c8411f

Provenance: formalization of a published result. Source: EconCSLib, `Minimax.symMat_skew`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Minimax.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Minimax.symMat_skew
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Nonempty I] [Nonempty J] in
theorem Minimax.symMat_skew (A : I → J → 𝕜) : ∀ k l, symMat A k l = - symMat A l k := by
  rintro (i | (j | _)) (i' | (j' | _)) <;> simp [symMat]
