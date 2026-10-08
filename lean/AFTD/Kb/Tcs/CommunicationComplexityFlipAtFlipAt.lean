import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityBoolInput
import AFTD.Kb.Tcs.CommunicationComplexityFlipAt
import AFTD.Kb.Tcs.CommunicationComplexityFlipAtApplySame
import AFTD.Kb.Tcs.CommunicationComplexityFlipAtApplyNe

/-!
# CommunicationComplexity.flipAt_flipAt

Topic: communication   Node: a7d18e0a4cb4

Provenance: helper lemma. TCSlib, `CommunicationComplexity.flipAt_flipAt`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Single-coordinate flip is an involution. Fix $n \in \bbn$, a coordinate $i \in \mathrm{Fin}\,n$, and an $n$-bit Boolean input $x
\colon \mathrm{Fin}\,n \to \mathrm{Bool}$. Writing $\mathrm{flip}_i$ for the operation
that negates the $i$-th coordinate of an input and leaves all other coordinates
unchanged, applying it twice recovers the original input:
\[
\mathrm{flip}_i\bigl(\mathrm{flip}_i(x)\bigr) = x.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Flipping the same coordinate twice returns the original input. -/
@[simp] lemma CommunicationComplexity.flipAt_flipAt {n : ℕ} (i : Fin n) (x : BoolInput n) :
    flipAt i (flipAt i x) = x := by
  ext j
  by_cases hij : j = i
  · subst hij
    simp [flipAt]
  · simp [flipAt, hij]
