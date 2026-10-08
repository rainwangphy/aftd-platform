import AFTD.Prelude

/-!
# IsKKMCover

Topic: general_equilibrium   Node: 9acd4db1ff2e

Provenance: formalization of a published result. Source: EconCSLib, `IsKKMCover`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/KKM.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The **KKM condition** for a cover `F : Fin n → Set _` of the standard simplex: for each subset `σ ⊆ Fin n`, the face of the simplex supported on `σ` (points with zero weight outside `σ`) is covered by `⋃_{i ∈ σ} F i`. This is the combinatorial heart of the KKM lemma: each face is covered by the subfamily indexed by that face's vertices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Finset in
variable {n : ℕ} in
/-- The **KKM condition** for a cover `F : Fin n → Set _` of the standard simplex: for each subset `σ ⊆ Fin n`, the face of the simplex supported on `σ` (points with zero weight outside `σ`) is covered by `⋃_{i ∈ σ} F i`. This is the combinatorial heart of the KKM lemma: each face is covered by the subfamily indexed by that face's vertices. -/
def IsKKMCover (F : Fin n → Set (Fin n → ℝ)) : Prop :=
  ∀ (σ : Finset (Fin n)),
    (stdSimplex ℝ (Fin n) ∩ {x | ∀ i ∉ σ, x i = 0}) ⊆ ⋃ i ∈ σ, F i
