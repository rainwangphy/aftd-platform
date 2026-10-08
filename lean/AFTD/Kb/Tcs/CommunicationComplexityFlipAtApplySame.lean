import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityBoolInput
import AFTD.Kb.Tcs.CommunicationComplexityFlipAt

/-!
# CommunicationComplexity.flipAt_apply_same

Topic: communication   Node: 07c1dfccd62f

Provenance: helper lemma. TCSlib, `CommunicationComplexity.flipAt_apply_same`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Value of the single-coordinate flip at the flipped coordinate. Let $n \in \bbn$, let $i \in \mathrm{Fin}\,n$ be a coordinate index, and let $x$ be an
$n$-bit Boolean input. The single-coordinate flip of $x$ at $i$ — the input obtained
from $x$ by negating its $i$-th coordinate and leaving all others unchanged — has value
$\neg\,x_i$ at coordinate $i$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Flipping coordinate `i` negates the value at coordinate `i`. -/
@[simp] lemma CommunicationComplexity.flipAt_apply_same {n : ℕ} (i : Fin n) (x : BoolInput n) :
    flipAt i x i = !(x i) := by
  simp [flipAt]
