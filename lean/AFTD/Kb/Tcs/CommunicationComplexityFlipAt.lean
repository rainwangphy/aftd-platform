import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityBoolInput

/-!
# CommunicationComplexity.flipAt

Topic: communication   Node: 42f5fc4d3ba9

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.flipAt`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given $i : \mathrm{Fin}\,n$ and $x : \texttt{BoolInput}(n)$, $\texttt{flipAt}\,i\,x$ is
the Boolean input obtained from $x$ by negating the $i$-th coordinate and leaving all
other coordinates unchanged.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Flipping one coordinate of a Boolean input. -/
def CommunicationComplexity.flipAt {n : ℕ} (i : Fin n) (x : BoolInput n) : BoolInput n :=
  Function.update x i (!(x i))
