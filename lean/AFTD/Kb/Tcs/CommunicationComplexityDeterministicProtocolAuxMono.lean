import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxAliceBit
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxBobBit
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesAux

/-!
# CommunicationComplexity.Deterministic.Protocol.aux_mono

Topic: communication   Node: 2594799b468a

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.aux_mono`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Leaf rectangles are output-monochromatic. Let $p$ be a deterministic communication protocol over input types $X$ (Alice) and $Y$
(Bob) with outputs in $\alpha$, and let $A \subseteq X$ and $B \subseteq Y$. If $R$ is
one of the auxiliary leaf rectangles of $p$ constrained to $A \times B$, and $(x, y)$
and $(x', y')$ both belong to $R$, then running $p$ yields the same output at both
inputs; that is, $p(x, y) = p(x', y')$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- The protocol output is constant on each leaf rectangle of `p` relative to `A ×ˢ B`. **Proof sketch.** Induction on `p`. A terminal protocol outputs a constant. Step 1: at an Alice node the rectangle `R` comes from one child, and both inputs in `R` send the bit of that child (`aux_alice_bit`), so both runs descend into the same child, where the induction hypothesis applies. Step 2: a Bob node is the mirror image with Bob's bit. -/
lemma CommunicationComplexity.Deterministic.Protocol.aux_mono (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B)
    (x x' : X) (y y' : Y) (hxy : (x, y) ∈ R) (hxy' : (x', y') ∈ R) :
    p.run x y = p.run x' y' := by
  induction p generalizing A B with
  | output v => rfl
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    -- Step 1: both inputs send the same bit, so the run descends into the same child.
    rcases hR with hR | hR <;>
      simp only [run, aux_alice_bit hR hxy, aux_alice_bit hR hxy'] <;> exact ih _ _ _ hR
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    -- Step 2: mirror of Step 1 for Bob's bit.
    rcases hR with hR | hR <;>
      simp only [run, aux_bob_bit hR hxy, aux_bob_bit hR hxy'] <;> exact ih _ _ _ hR
