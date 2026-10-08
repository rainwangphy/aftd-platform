import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityBoolInput
import AFTD.Kb.Tcs.CommunicationComplexityFlipAt
import AFTD.Kb.Tcs.CommunicationComplexityFlipAtApplySame

/-!
# CommunicationComplexity.flipAt_apply_ne

Topic: communication   Node: 4453bfd52e6b

Provenance: helper lemma. TCSlib, `CommunicationComplexity.flipAt_apply_ne`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Flip leaves other coordinates unchanged. Let $x \colon \mathrm{Fin}\,n \to \mathrm{Bool}$ be an $n$-bit Boolean input, and let
$i, j \in \mathrm{Fin}\,n$ be coordinates with $j \ne i$. Then the input obtained from
$x$ by flipping its $i$-th coordinate agrees with $x$ at coordinate $j$; that is, its
value at $j$ equals $x(j)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Flipping coordinate `i` leaves every other coordinate `j ≠ i` unchanged. -/
@[simp] lemma CommunicationComplexity.flipAt_apply_ne {n : ℕ} {i j : Fin n} (hij : j ≠ i) (x : BoolInput n) :
    flipAt i x j = x j := by
  simp [flipAt, hij]
