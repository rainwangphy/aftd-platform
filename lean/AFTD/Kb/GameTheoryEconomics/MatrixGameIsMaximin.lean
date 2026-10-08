import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameEj

/-!
# MatrixGame.IsMaximin

Topic: equilibria   Node: d4f95f902b02

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.IsMaximin`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`v` is a **maximin value** of `A`: some row strategy guarantees at least `v` (existence), and no strictly larger value is achievable (maximality).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable (A : MatrixGame I J 𝕜) in
/-- `v` is a **maximin value** of `A`: some row strategy guarantees at least `v` (existence), and no strictly larger value is achievable (maximality). -/
def MatrixGame.IsMaximin (A : MatrixGame I J 𝕜) (v : 𝕜) : Prop :=
  (∃ x : stdSimplex 𝕜 I, ∀ j, v ≤ A.Ej x j) ∧
  (∀ w, (∃ x : stdSimplex 𝕜 I, ∀ j, w ≤ A.Ej x j) → w ≤ v)
