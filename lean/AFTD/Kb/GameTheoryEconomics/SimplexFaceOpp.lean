import AFTD.Prelude

/-!
# simplexFaceOpp

Topic: general_equilibrium   Node: 3a1d9d96149f

Provenance: formalization of a published result. Source: EconCSLib, `simplexFaceOpp`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/KKM.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The **face of the standard simplex opposite vertex `i`**: the set of simplex points whose `i`-th coordinate is zero. In cake-cutting language (Stromquist 1980): `simplexFaceOpp i` is the face `Sᵢ` consisting of all divisions where the `i`-th piece has measure zero (is "empty"). The KKM open-cover condition requires `Uᵢ ∩ simplexFaceOpp i = ∅` — no division in `Uᵢ` has an empty `i`-th piece.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Finset in
variable {n : ℕ} in
/-- The **face of the standard simplex opposite vertex `i`**: the set of simplex points whose `i`-th coordinate is zero. In cake-cutting language (Stromquist 1980): `simplexFaceOpp i` is the face `Sᵢ` consisting of all divisions where the `i`-th piece has measure zero (is "empty"). The KKM open-cover condition requires `Uᵢ ∩ simplexFaceOpp i = ∅` — no division in `Uᵢ` has an empty `i`-th piece. -/
def simplexFaceOpp (i : Fin n) : Set (Fin n → ℝ) :=
  {x | x i = 0} ∩ stdSimplex ℝ (Fin n)
