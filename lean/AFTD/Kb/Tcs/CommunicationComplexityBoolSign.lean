import AFTD.Prelude

/-!
# CommunicationComplexity.boolSign

Topic: communication   Node: b351f414f203

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.boolSign`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\texttt{boolSign} : \mathrm{Bool} \to \mathbb{R}$ assigns the real value $1$ to
$\mathrm{false}$ and $-1$ to $\mathrm{true}$, embedding Boolean values into the
multiplicative group $\{\pm 1\} \subset \mathbb{R}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The `±1` sign attached to a Boolean value. We use `1` for `false` and `-1` for `true`, i.e. the encoding `b ↦ (-1)^b` of [OD14, §1.1]. -/
def CommunicationComplexity.boolSign (b : Bool) : ℝ :=
  if b then -1 else 1
