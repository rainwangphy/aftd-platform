import AFTD.Prelude

/-!
# stdSimplex.affineCombination

Topic: lp_duality   Node: 17d0daa0f518

Provenance: formalization of a published result. Source: EconCSLib, `stdSimplex.affineCombination`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Affine combination of a finite family of points using simplex weights. This is a thin wrapper around Mathlib's `Finset.affineCombination`, specialized to weights coming from `stdSimplex`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Affine combination of a finite family of points using simplex weights. This is a thin wrapper around Mathlib's `Finset.affineCombination`, specialized to weights coming from `stdSimplex`. -/
noncomputable def stdSimplex.affineCombination {k V P I : Type*}
    [Ring k] [PartialOrder k] [Fintype I]
    [AddCommGroup V] [Module k V] [AddTorsor V P]
    (x : stdSimplex k I) (p : I → P) : P :=
  Finset.univ.affineCombination k p x
