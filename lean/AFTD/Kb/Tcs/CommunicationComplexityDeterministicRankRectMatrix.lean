import AFTD.Prelude

/-!
# CommunicationComplexity.Deterministic.Rank.rectMatrix

Topic: communication   Node: 033b52a5e650

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.Rank.rectMatrix`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rank.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a subset $R \subseteq X \times Y$, the matrix $M_R \in \mathbb{R}^{X \times Y}$
is defined by $(M_R)_{x,y} = 1$ if $(x,y) \in R$ and $(M_R)_{x,y} = 0$ otherwise.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Classical in
/-- The `0/1` indicator matrix of a subset `R ⊆ X × Y`: the `(x, y)` entry is `1` if `(x, y) ∈ R` and `0` otherwise. -/
noncomputable def CommunicationComplexity.Deterministic.Rank.rectMatrix {X Y : Type*}
    (R : Set (X × Y)) : Matrix X Y ℝ :=
  Matrix.of fun x y => if (x, y) ∈ R then 1 else 0
