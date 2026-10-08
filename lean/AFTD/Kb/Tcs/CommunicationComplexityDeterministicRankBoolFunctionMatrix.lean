import AFTD.Prelude

/-!
# CommunicationComplexity.Deterministic.Rank.boolFunctionMatrix

Topic: communication   Node: ef0f0ca7ac9e

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.Rank.boolFunctionMatrix`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rank.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a Boolean function $f : X \to Y \to \mathrm{Bool}$, the matrix
$M_f \in \mathbb{R}^{X \times Y}$ is defined by $(M_f)_{x,y} = 1$ if
$f\,x\,y = \mathrm{true}$ and $(M_f)_{x,y} = 0$ otherwise.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Classical in
/-- The real-valued communication matrix of a Boolean function `f : X → Y → Bool`, whose `(x, y)` entry is `1` if `f x y = true` and `0` otherwise [RY20, Ch. 2] / [Rou16, §4.2.3 Definition (matrix representation)]. -/
noncomputable def CommunicationComplexity.Deterministic.Rank.boolFunctionMatrix {X Y : Type*}
    (f : X → Y → Bool) : Matrix X Y ℝ :=
  Matrix.of fun x y => if f x y then 1 else 0
